import Formal.AG.LawAlgebra.ObstructionIdeal
import Formal.AG.Site
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace AAT.AG
namespace LawAlgebra

open CategoryTheory
open Opposite

universe u

/-! ## III.定義11.3 / III.定理11.4: laws as generated equation coefficients -/

/--
III.定義11.3: law-equation witness-ideal core.

`Observable` is a ring-valued observable presheaf on the selected AAT site.
Each law is realized by atom-indexed violation coordinates, and those
coordinates are compatible with context restriction.  The structure stores no
interpretation map, quotient vanishing premise, Cech data, or global repair
certificate.
-/
structure SemanticLawEquationWitnessIdealCore
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  Observable : S.category -> Type u
  observableCommRing : forall W : S.category, CommRing (Observable W)
  restrict :
    forall {source target : S.category},
      (source ⟶ target) -> Observable target →+* Observable source
  restrict_id :
    forall (W : S.category) (x : Observable W), restrict (𝟙 W) x = x
  restrict_comp :
    forall {W₀ W₁ W₂ : S.category} (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
      (x : Observable W₂),
      restrict (f ≫ g) x = restrict f (restrict g x)
  violationWitness :
    forall (W : S.category), S.equationSystem.Index -> U.Atom -> Observable W
  violationWitness_restrict :
    forall {source target : S.category} (f : source ⟶ target)
      (lawIndex : S.equationSystem.Index) (atom : U.Atom),
      restrict f (violationWitness target lawIndex atom) =
        violationWitness source lawIndex atom
  supportAtom : U.Atom
  supportLawIndex : S.equationSystem.Index
  supportLawIndex_required : S.equationSystem.Required supportLawIndex

attribute [instance] SemanticLawEquationWitnessIdealCore.observableCommRing

namespace SemanticLawEquationWitnessIdealCore

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/--
III.定義11.3: the witness ideal of one law is the span of its atom-indexed
violation coordinates.
-/
def lawWitnessIdeal
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) (lawIndex : S.equationSystem.Index) :
    Ideal (G.Observable W) :=
  Ideal.span (Set.range (G.violationWitness W lawIndex))

/-- III.定義11.3: selected required-law witness ideals at one context. -/
def selectedLawWitnessIdealFamily
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) :
    ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, u} (G.Observable W) where
  LawIndex := S.equationSystem.Index
  selected := S.equationSystem.Required
  witnessIdeal := G.lawWitnessIdeal W

/-- III.定義11.3: local obstruction ideal `I_Ob(W) = Σ_L I_L(W)`. -/
def obstructionIdeal
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) : Ideal (G.Observable W) :=
  (G.selectedLawWitnessIdealFamily W).localObstructionIdeal

/-- Required law witness ideals are contained in the generated local obstruction ideal. -/
theorem lawWitnessIdeal_le_obstructionIdeal
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) {lawIndex : S.equationSystem.Index}
    (hrequired : S.equationSystem.Required lawIndex) :
    G.lawWitnessIdeal W lawIndex ≤ G.obstructionIdeal W :=
  ObstructionIdeal.SelectedLawWitnessIdealFamily.witnessIdeal_le_localObstructionIdeal
    (G.Observable W) (G.selectedLawWitnessIdealFamily W) hrequired

/--
III.定理11.4: restriction maps each law witness ideal into the corresponding
witness ideal on the restricted context.
-/
theorem map_lawWitnessIdeal_le
    (G : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target)
    (lawIndex : S.equationSystem.Index) :
    Ideal.map (G.restrict f) (G.lawWitnessIdeal target lawIndex) ≤
      G.lawWitnessIdeal source lawIndex := by
  rw [lawWitnessIdeal, Ideal.map_span]
  refine Ideal.span_mono ?_
  rintro x ⟨y, ⟨atom, rfl⟩, rfl⟩
  exact ⟨atom, (G.violationWitness_restrict f lawIndex atom).symm⟩

/-- III.定理11.4: selected witness ideals are restriction-compatible. -/
def restrictionCompatible
    (G : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target) :
    ObstructionIdeal.SelectedLawWitnessIdealFamily.RestrictionCompatible
      (G.selectedLawWitnessIdealFamily target)
      (G.selectedLawWitnessIdealFamily source)
      (G.restrict f) where
  maps_selected := fun lawIndex hselected =>
    ⟨lawIndex, hselected, G.map_lawWitnessIdeal_le f lawIndex⟩

/-- III.定理11.4: restriction maps local obstruction ideals into local obstruction ideals. -/
theorem map_obstructionIdeal_le
    (G : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target) :
    Ideal.map (G.restrict f) (G.obstructionIdeal target) ≤
      G.obstructionIdeal source :=
  ObstructionIdeal.SelectedLawWitnessIdealFamily.map_localObstructionIdeal_le
    (G.restrictionCompatible f)

/-- III.定理11.4: generated obstruction quotient carrier `O(W) / I_Ob(W)`. -/
abbrev ObstructionQuotient
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) : Type u :=
  G.Observable W ⧸ G.obstructionIdeal W

/-- III.定理11.4: generated restriction map on obstruction quotients. -/
def obstructionQuotientRestrict
    (G : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target) :
    G.ObstructionQuotient target →+* G.ObstructionQuotient source :=
  Ideal.quotientMap (G.obstructionIdeal source) (G.restrict f)
    (Ideal.map_le_iff_le_comap.mp (G.map_obstructionIdeal_le f))

/-- III.定理11.4: quotient restriction is induced by restricting representatives. -/
theorem obstructionQuotientRestrict_mk
    (G : SemanticLawEquationWitnessIdealCore S)
    {source target : S.category} (f : source ⟶ target)
    (x : G.Observable target) :
    G.obstructionQuotientRestrict f
        (Ideal.Quotient.mk (G.obstructionIdeal target) x) =
      Ideal.Quotient.mk (G.obstructionIdeal source) (G.restrict f x) := by
  simp [obstructionQuotientRestrict]

/--
III.定理11.4: generated additive-group-valued obstruction coefficient
presheaf.  The identity and composition laws are proved from the observable
restriction laws.
-/
def obstructionQuotientCoefficient
    (G : SemanticLawEquationWitnessIdealCore S) :
    S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (G.ObstructionQuotient W.unop)
  map {X Y} φ :=
    AddCommGrpCat.ofHom (G.obstructionQuotientRestrict φ.unop).toAddMonoidHom
  map_id X := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro r
    show G.obstructionQuotientRestrict (𝟙 X.unop)
        (Ideal.Quotient.mk (G.obstructionIdeal X.unop) r) =
      Ideal.Quotient.mk (G.obstructionIdeal X.unop) r
    rw [G.obstructionQuotientRestrict_mk, G.restrict_id]
  map_comp {X Y Z} φ ψ := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro r
    show G.obstructionQuotientRestrict (ψ.unop ≫ φ.unop)
        (Ideal.Quotient.mk (G.obstructionIdeal X.unop) r) =
      G.obstructionQuotientRestrict ψ.unop
        (G.obstructionQuotientRestrict φ.unop
          (Ideal.Quotient.mk (G.obstructionIdeal X.unop) r))
    rw [G.obstructionQuotientRestrict_mk, G.obstructionQuotientRestrict_mk,
      G.obstructionQuotientRestrict_mk, G.restrict_comp]

/--
III.定理11.4 / X.定義5.1: the same generated obstruction quotient, exposed as
the Type-valued AAT presheaf used by semantic-repair theorem 7.5.

This is definitionally generated from `O(W) / I_Ob(W)` and its quotient
restriction maps; it is not an arbitrary supplied coefficient presheaf.
-/
def obstructionQuotientPresheaf
    (G : SemanticLawEquationWitnessIdealCore S) :
    Site.AATPresheaf S :=
  G.obstructionQuotientCoefficient ⋙ forget AddCommGrpCat.{u}

@[simp]
theorem obstructionQuotientPresheaf_eq_forget_coefficient
    (G : SemanticLawEquationWitnessIdealCore S) :
    G.obstructionQuotientPresheaf =
      G.obstructionQuotientCoefficient ⋙ forget AddCommGrpCat.{u} :=
  rfl

/-- III.定理11.4: quotient zero is exactly local obstruction ideal membership. -/
theorem quotient_mk_eq_zero_iff_mem_obstructionIdeal
    (G : SemanticLawEquationWitnessIdealCore S)
    (W : S.category) (x : G.Observable W) :
    Ideal.Quotient.mk (G.obstructionIdeal W) x = 0 <->
      x ∈ G.obstructionIdeal W :=
  Ideal.Quotient.eq_zero_iff_mem

/-- III.定理11.4 package: generated witness ideals and quotient coefficient laws. -/
theorem generatedCoefficient_package
    (G : SemanticLawEquationWitnessIdealCore S) :
    (forall W (lawIndex : S.equationSystem.Index),
      S.equationSystem.Required lawIndex ->
        G.lawWitnessIdeal W lawIndex ≤ G.obstructionIdeal W) /\
      (forall {source target : S.category} (f : source ⟶ target)
        (lawIndex : S.equationSystem.Index),
        Ideal.map (G.restrict f) (G.lawWitnessIdeal target lawIndex) ≤
          G.lawWitnessIdeal source lawIndex) /\
      (forall {source target : S.category} (f : source ⟶ target),
        Ideal.map (G.restrict f) (G.obstructionIdeal target) ≤
          G.obstructionIdeal source) /\
      (forall W (x : G.Observable W),
        Ideal.Quotient.mk (G.obstructionIdeal W) x = 0 <->
          x ∈ G.obstructionIdeal W) :=
  ⟨fun W _lawIndex hrequired => G.lawWitnessIdeal_le_obstructionIdeal W hrequired,
    fun {_source _target} f lawIndex =>
      G.map_lawWitnessIdeal_le f lawIndex,
    fun {_source _target} f =>
      G.map_obstructionIdeal_le f,
    fun W x => G.quotient_mk_eq_zero_iff_mem_obstructionIdeal W x⟩

end SemanticLawEquationWitnessIdealCore

/--
III.定理11.4: displayed local law-equation defect source.

The interpretation is generated as the obstruction quotient class of
`defect`; it is not a field.  The law-as-equation tie is chart-local: a
displayed required law holding on the displayed local reading places the
defect in that law's witness ideal.
-/
structure LawEquationDefectSource
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (G : SemanticLawEquationWitnessIdealCore S) where
  Chart : Type u
  chart : Chart -> S.category
  LocalInput : Chart -> Type u
  input : (i : Chart) -> LocalInput i
  lawSupport : (i : Chart) -> LocalInput i -> List S.equationSystem.Index
  lawSupport_nonempty :
    forall i, exists lawIndex : S.equationSystem.Index,
      lawIndex ∈ lawSupport i (input i)
  lawSupport_required :
    forall i (lawIndex : S.equationSystem.Index),
      lawIndex ∈ lawSupport i (input i) -> S.equationSystem.Required lawIndex
  objectOfLocalInput : (i : Chart) -> LocalInput i -> ArchitectureObject U
  defect : (i : Chart) -> LocalInput i -> G.Observable (chart i)
  holds_defect_mem :
    forall i (lawIndex : S.equationSystem.Index),
      lawIndex ∈ lawSupport i (input i) ->
        S.equationSystem.Required lawIndex ->
          S.equationSystem.EquationHolds lawIndex
            (objectOfLocalInput i (input i)) ->
            defect i (input i) ∈ G.lawWitnessIdeal (chart i) lawIndex

namespace LawEquationDefectSource

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {G : SemanticLawEquationWitnessIdealCore S}

/-- Generated interpretation as the obstruction quotient class of the displayed defect. -/
def interpret (D : LawEquationDefectSource G) (i : D.Chart) :
    G.ObstructionQuotient (D.chart i) :=
  Ideal.Quotient.mk (G.obstructionIdeal (D.chart i))
    (D.defect i (D.input i))

/-- Displayed required laws hold on all selected local readings. -/
def DisplayedRequiredLawsHoldOn (D : LawEquationDefectSource G) : Prop :=
  forall i (lawIndex : S.equationSystem.Index),
    lawIndex ∈ D.lawSupport i (D.input i) ->
      S.equationSystem.Required lawIndex ->
        S.equationSystem.EquationHolds lawIndex
          (D.objectOfLocalInput i (D.input i))

/-- Pointwise zero of the generated quotient interpretation. -/
def GeneratedInterpretationPointwiseZero (D : LawEquationDefectSource G) : Prop :=
  forall i, D.interpret i = 0

/--
III.定理11.4: if displayed required laws hold, every generated interpretation
is zero in the obstruction quotient.
-/
theorem displayedRequiredLawsHoldOn_constructs_interpret_eq_zero
    (D : LawEquationDefectSource G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    forall i : D.Chart, D.interpret i = 0 := by
  intro i
  obtain ⟨lawIndex, hmem⟩ := D.lawSupport_nonempty i
  have hrequired : S.equationSystem.Required lawIndex :=
    D.lawSupport_required i lawIndex hmem
  have hholdsLaw :
      S.equationSystem.EquationHolds lawIndex
        (D.objectOfLocalInput i (D.input i)) :=
    hholds i lawIndex hmem hrequired
  have hdefect :
      D.defect i (D.input i) ∈ G.lawWitnessIdeal (D.chart i) lawIndex :=
    D.holds_defect_mem i lawIndex hmem hrequired hholdsLaw
  have hobstruction :
      D.defect i (D.input i) ∈ G.obstructionIdeal (D.chart i) :=
    G.lawWitnessIdeal_le_obstructionIdeal (D.chart i) hrequired hdefect
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hobstruction

/-- III.定理11.4: generated interpretation vanishes iff the defect is in `I_Ob`. -/
theorem interpret_eq_zero_iff_defect_mem_obstructionIdeal
    (D : LawEquationDefectSource G)
    (i : D.Chart) :
    D.interpret i = 0 <->
      D.defect i (D.input i) ∈ G.obstructionIdeal (D.chart i) :=
  Ideal.Quotient.eq_zero_iff_mem

/-- III.定理11.4: a defect outside `I_Ob` gives a nonzero generated interpretation. -/
theorem interpret_ne_zero_of_defect_notMem_obstructionIdeal
    (D : LawEquationDefectSource G)
    (i : D.Chart)
    (hnot : D.defect i (D.input i) ∉ G.obstructionIdeal (D.chart i)) :
    D.interpret i ≠ 0 :=
  fun hzero => hnot ((D.interpret_eq_zero_iff_defect_mem_obstructionIdeal i).mp hzero)

/--
III.定理11.4: detector soundness.  A nonzero generated interpretation rules
out every displayed required law on that local reading.
-/
theorem interpret_ne_zero_detects_displayed_required_law_failure
    (D : LawEquationDefectSource G)
    (i : D.Chart)
    (hne : D.interpret i ≠ 0) :
    forall lawIndex : S.equationSystem.Index,
      lawIndex ∈ D.lawSupport i (D.input i) ->
        S.equationSystem.Required lawIndex ->
          ¬ S.equationSystem.EquationHolds lawIndex
              (D.objectOfLocalInput i (D.input i)) := by
  intro lawIndex hmem hrequired hholdsLaw
  refine hne ?_
  have hdefect :
      D.defect i (D.input i) ∈ G.lawWitnessIdeal (D.chart i) lawIndex :=
    D.holds_defect_mem i lawIndex hmem hrequired hholdsLaw
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (G.lawWitnessIdeal_le_obstructionIdeal (D.chart i) hrequired hdefect)

/-- III.定理11.4: displayed law fulfillment constructs pointwise interpretation zero. -/
theorem displayedRequiredLawsHoldOn_constructs_generatedInterpretationPointwiseZero
    (D : LawEquationDefectSource G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    D.GeneratedInterpretationPointwiseZero :=
  D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds

/-- III.定理11.4 package: law-equation grounding for generated coefficients. -/
theorem lawEquation_grounding_packet
    (D : LawEquationDefectSource G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    (forall i : D.Chart, D.interpret i = 0) /\
      D.GeneratedInterpretationPointwiseZero /\
      (forall i : D.Chart,
        D.interpret i = 0 <->
          D.defect i (D.input i) ∈ G.obstructionIdeal (D.chart i)) /\
      (forall i : D.Chart,
        D.interpret i ≠ 0 ->
          forall lawIndex : S.equationSystem.Index,
            lawIndex ∈ D.lawSupport i (D.input i) ->
              S.equationSystem.Required lawIndex ->
                ¬ S.equationSystem.EquationHolds lawIndex
                    (D.objectOfLocalInput i (D.input i))) :=
  ⟨D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds,
    D.displayedRequiredLawsHoldOn_constructs_generatedInterpretationPointwiseZero hholds,
    D.interpret_eq_zero_iff_defect_mem_obstructionIdeal,
    fun i hne =>
      D.interpret_ne_zero_detects_displayed_required_law_failure i hne⟩

end LawEquationDefectSource

end LawAlgebra
end AAT.AG
