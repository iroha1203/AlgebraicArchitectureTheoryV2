import Formal.AG.LawAlgebra.ObstructionIdeal
import Formal.AG.Site
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace AAT.AG

open CategoryTheory
open Opposite

universe u

/-! ## III.定義11.3 / III.定理11.4: laws as generated equation coefficients -/

namespace ArchitecturalEquationSystem

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A}

/--
III.定義11.3: the witness ideal of one equation is the span of its atom-indexed
violation coordinates.
-/
def witnessIdeal
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) (equationIndex : E.Index) :
    Ideal (E.Observable W) :=
  Ideal.span (Set.range (E.violationCoordinate W equationIndex))

/-- The generated witness ideal is definitionally the span of the selected coordinates. -/
@[simp] theorem witnessIdeal_eq_span
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) (equationIndex : E.Index) :
    E.witnessIdeal W equationIndex =
      Ideal.span (Set.range (E.violationCoordinate W equationIndex)) :=
  rfl

/-- III.定義11.3: selected required-equation witness ideals at one context. -/
def selectedWitnessIdealFamily
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) :
    LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, u} (E.Observable W) where
  LawIndex := E.Index
  selected := E.Required
  witnessIdeal := E.witnessIdeal W

/-- III.定義11.3: local obstruction ideal `I_Ob(W) = Σ_L I_L(W)`. -/
def obstructionIdeal
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) : Ideal (E.Observable W) :=
  (E.selectedWitnessIdealFamily W).localObstructionIdeal

/-- III.定義11.3: the obstruction ideal is the supremum of required witness ideals. -/
theorem obstructionIdeal_eq_iSup_required
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) :
    E.obstructionIdeal W =
      ⨆ equationIndex : E.RequiredIndex, E.witnessIdeal W equationIndex.1 :=
  LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_eq_iSup
    (E.Observable W) (E.selectedWitnessIdealFamily W)

/-- Required equation witness ideals are contained in the generated obstruction ideal. -/
theorem witnessIdeal_le_obstructionIdeal
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) {equationIndex : E.Index}
    (hrequired : E.Required equationIndex) :
    E.witnessIdeal W equationIndex ≤ E.obstructionIdeal W :=
  LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.witnessIdeal_le_localObstructionIdeal
    (E.Observable W) (E.selectedWitnessIdealFamily W) hrequired

/--
III.定理11.4: restriction maps each equation witness ideal into the corresponding
witness ideal on the restricted context.
-/
theorem map_witnessIdeal_le
    (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
    (equationIndex : E.Index) :
    Ideal.map (E.restrict f) (E.witnessIdeal target equationIndex) ≤
      E.witnessIdeal source equationIndex := by
  rw [witnessIdeal, Ideal.map_span]
  refine Ideal.span_mono ?_
  rintro x ⟨y, ⟨atom, rfl⟩, rfl⟩
  exact ⟨atom, (E.violationCoordinate_restrict f equationIndex atom).symm⟩

/-- III.定理11.4: selected witness ideals are restriction-compatible. -/
def restrictionCompatible
    (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target) :
    LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.RestrictionCompatible
      (E.selectedWitnessIdealFamily target)
      (E.selectedWitnessIdealFamily source)
      (E.restrict f) where
  maps_selected := fun equationIndex hselected =>
    ⟨equationIndex, hselected, E.map_witnessIdeal_le f equationIndex⟩

/-- III.定理11.4: restriction maps local obstruction ideals into local obstruction ideals. -/
theorem map_obstructionIdeal_le
    (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target) :
    Ideal.map (E.restrict f) (E.obstructionIdeal target) ≤
      E.obstructionIdeal source :=
  LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.map_localObstructionIdeal_le
    (E.restrictionCompatible f)

/-- III.定理11.4: generated obstruction quotient carrier `O(W) / I_Ob(W)`. -/
abbrev ObstructionQuotient
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) : Type u :=
  E.Observable W ⧸ E.obstructionIdeal W

/-- III.定理11.4: generated restriction map on obstruction quotients. -/
def obstructionQuotientRestrict
    (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target) :
    E.ObstructionQuotient target →+* E.ObstructionQuotient source :=
  Ideal.quotientMap (E.obstructionIdeal source) (E.restrict f)
    (Ideal.map_le_iff_le_comap.mp (E.map_obstructionIdeal_le f))

/-- III.定理11.4: quotient restriction is induced by restricting representatives. -/
theorem obstructionQuotientRestrict_mk
    (E : ArchitecturalEquationSystem C)
    {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
    (x : E.Observable target) :
    E.obstructionQuotientRestrict f
        (Ideal.Quotient.mk (E.obstructionIdeal target) x) =
      Ideal.Quotient.mk (E.obstructionIdeal source) (E.restrict f x) := by
  simp [obstructionQuotientRestrict]

/-- III.定理11.4: quotient restriction along an identity is the identity. -/
@[simp] theorem obstructionQuotientRestrict_id_apply
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) (x : E.ObstructionQuotient W) :
    E.obstructionQuotientRestrict (𝟙 W) x = x := by
  refine Quotient.inductionOn' x ?_
  intro representative
  show E.obstructionQuotientRestrict (𝟙 W)
      (Ideal.Quotient.mk (E.obstructionIdeal W) representative) =
    Ideal.Quotient.mk (E.obstructionIdeal W) representative
  rw [E.obstructionQuotientRestrict_mk, E.restrict_id]

/-- III.定理11.4: quotient restriction respects composition. -/
theorem obstructionQuotientRestrict_comp_apply
    (E : ArchitecturalEquationSystem C)
    {W₀ W₁ W₂ : Site.ContextCategoryObject C}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂) (x : E.ObstructionQuotient W₂) :
    E.obstructionQuotientRestrict (f ≫ g) x =
      E.obstructionQuotientRestrict f (E.obstructionQuotientRestrict g x) := by
  refine Quotient.inductionOn' x ?_
  intro representative
  show E.obstructionQuotientRestrict (f ≫ g)
      (Ideal.Quotient.mk (E.obstructionIdeal W₂) representative) =
    E.obstructionQuotientRestrict f
      (E.obstructionQuotientRestrict g
        (Ideal.Quotient.mk (E.obstructionIdeal W₂) representative))
  rw [E.obstructionQuotientRestrict_mk, E.obstructionQuotientRestrict_mk,
    E.obstructionQuotientRestrict_mk, E.restrict_comp]

/--
III.定理11.4: generated additive-group-valued obstruction coefficient
presheaf.  The identity and composition laws are proved from the observable
restriction laws.
-/
def obstructionQuotientCoefficient
    (E : ArchitecturalEquationSystem C) :
    (Site.ContextCategoryObject C)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (E.ObstructionQuotient W.unop)
  map {X Y} φ :=
    AddCommGrpCat.ofHom (E.obstructionQuotientRestrict φ.unop).toAddMonoidHom
  map_id X := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro r
    show E.obstructionQuotientRestrict (𝟙 X.unop)
        (Ideal.Quotient.mk (E.obstructionIdeal X.unop) r) =
      Ideal.Quotient.mk (E.obstructionIdeal X.unop) r
    rw [E.obstructionQuotientRestrict_mk, E.restrict_id]
  map_comp {X Y Z} φ ψ := by
    ext x
    refine Quotient.inductionOn' x ?_
    intro r
    show E.obstructionQuotientRestrict (ψ.unop ≫ φ.unop)
        (Ideal.Quotient.mk (E.obstructionIdeal X.unop) r) =
      E.obstructionQuotientRestrict ψ.unop
        (E.obstructionQuotientRestrict φ.unop
          (Ideal.Quotient.mk (E.obstructionIdeal X.unop) r))
    rw [E.obstructionQuotientRestrict_mk, E.obstructionQuotientRestrict_mk,
      E.obstructionQuotientRestrict_mk, E.restrict_comp]

/--
III.定理11.4 / X.定義5.1: the same generated obstruction quotient, exposed as
the Type-valued AAT presheaf used by semantic-repair theorem 7.5.

This is definitionally generated from `O(W) / I_Ob(W)` and its quotient
restriction maps; it is not an arbitrary supplied coefficient presheaf.
-/
def obstructionQuotientPresheaf
    {S : Site.AATSite A}
    (E : ArchitecturalEquationSystem S.contextPreorder) :
    Site.AATPresheaf S :=
  E.obstructionQuotientCoefficient ⋙ forget AddCommGrpCat.{u}

@[simp]
theorem obstructionQuotientPresheaf_eq_forget_coefficient
    {S : Site.AATSite A}
    (E : ArchitecturalEquationSystem S.contextPreorder) :
    E.obstructionQuotientPresheaf =
      E.obstructionQuotientCoefficient ⋙ forget AddCommGrpCat.{u} :=
  rfl

/-- III.定理11.4: quotient zero is exactly local obstruction ideal membership. -/
theorem quotient_mk_eq_zero_iff_mem_obstructionIdeal
    (E : ArchitecturalEquationSystem C)
    (W : Site.ContextCategoryObject C) (x : E.Observable W) :
    Ideal.Quotient.mk (E.obstructionIdeal W) x = 0 <->
      x ∈ E.obstructionIdeal W :=
  Ideal.Quotient.eq_zero_iff_mem

/-- III.定理11.4 package: generated witness ideals and quotient coefficient laws. -/
theorem generatedCoefficient_package
    (E : ArchitecturalEquationSystem C) :
    (forall W (equationIndex : E.Index),
      E.Required equationIndex ->
        E.witnessIdeal W equationIndex ≤ E.obstructionIdeal W) /\
      (forall {source target : Site.ContextCategoryObject C} (f : source ⟶ target)
        (equationIndex : E.Index),
        Ideal.map (E.restrict f) (E.witnessIdeal target equationIndex) ≤
          E.witnessIdeal source equationIndex) /\
      (forall {source target : Site.ContextCategoryObject C} (f : source ⟶ target),
        Ideal.map (E.restrict f) (E.obstructionIdeal target) ≤
          E.obstructionIdeal source) /\
      (forall W (x : E.Observable W),
        Ideal.Quotient.mk (E.obstructionIdeal W) x = 0 <->
          x ∈ E.obstructionIdeal W) :=
  ⟨fun W _equationIndex hrequired => E.witnessIdeal_le_obstructionIdeal W hrequired,
    fun {_source _target} f equationIndex =>
      E.map_witnessIdeal_le f equationIndex,
    fun {_source _target} f =>
      E.map_obstructionIdeal_le f,
    fun W x => E.quotient_mk_eq_zero_iff_mem_obstructionIdeal W x⟩

end ArchitecturalEquationSystem

namespace LawAlgebra

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
    (E : ArchitecturalEquationSystem S.contextPreorder) where
  Chart : Type u
  chart : Chart -> S.category
  LocalInput : Chart -> Type u
  input : (i : Chart) -> LocalInput i
  lawSupport : (i : Chart) -> LocalInput i -> List E.Index
  lawSupport_nonempty :
    forall i, exists equationIndex : E.Index,
      equationIndex ∈ lawSupport i (input i)
  lawSupport_required :
    forall i (equationIndex : E.Index),
      equationIndex ∈ lawSupport i (input i) -> E.Required equationIndex
  objectOfLocalInput : (i : Chart) -> LocalInput i -> ArchitectureObject U
  defect : (i : Chart) -> LocalInput i -> E.Observable (chart i)
  holds_defect_mem :
    forall i (equationIndex : E.Index),
      equationIndex ∈ lawSupport i (input i) ->
        E.Required equationIndex ->
          E.EquationHolds equationIndex
            (objectOfLocalInput i (input i)) ->
            defect i (input i) ∈ E.witnessIdeal (chart i) equationIndex

namespace LawEquationDefectSource

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : ArchitecturalEquationSystem S.contextPreorder}

/-- Generated interpretation as the obstruction quotient class of the displayed defect. -/
def interpret (D : LawEquationDefectSource E) (i : D.Chart) :
    E.ObstructionQuotient (D.chart i) :=
  Ideal.Quotient.mk (E.obstructionIdeal (D.chart i))
    (D.defect i (D.input i))

/-- Displayed required laws hold on all selected local readings. -/
def DisplayedRequiredLawsHoldOn (D : LawEquationDefectSource E) : Prop :=
  forall i (equationIndex : E.Index),
    equationIndex ∈ D.lawSupport i (D.input i) ->
      E.Required equationIndex ->
        E.EquationHolds equationIndex
          (D.objectOfLocalInput i (D.input i))

/-- Pointwise zero of the generated quotient interpretation. -/
def GeneratedInterpretationPointwiseZero (D : LawEquationDefectSource E) : Prop :=
  forall i, D.interpret i = 0

/--
III.定理11.4: if displayed required laws hold, every generated interpretation
is zero in the obstruction quotient.
-/
theorem displayedRequiredLawsHoldOn_constructs_interpret_eq_zero
    (D : LawEquationDefectSource E)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    forall i : D.Chart, D.interpret i = 0 := by
  intro i
  obtain ⟨equationIndex, hmem⟩ := D.lawSupport_nonempty i
  have hrequired : E.Required equationIndex :=
    D.lawSupport_required i equationIndex hmem
  have hholdsLaw :
      E.EquationHolds equationIndex
        (D.objectOfLocalInput i (D.input i)) :=
    hholds i equationIndex hmem hrequired
  have hdefect :
      D.defect i (D.input i) ∈ E.witnessIdeal (D.chart i) equationIndex :=
    D.holds_defect_mem i equationIndex hmem hrequired hholdsLaw
  have hobstruction :
      D.defect i (D.input i) ∈ E.obstructionIdeal (D.chart i) :=
    E.witnessIdeal_le_obstructionIdeal (D.chart i) hrequired hdefect
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hobstruction

/-- III.定理11.4: generated interpretation vanishes iff the defect is in `I_Ob`. -/
theorem interpret_eq_zero_iff_defect_mem_obstructionIdeal
    (D : LawEquationDefectSource E)
    (i : D.Chart) :
    D.interpret i = 0 <->
      D.defect i (D.input i) ∈ E.obstructionIdeal (D.chart i) :=
  Ideal.Quotient.eq_zero_iff_mem

/-- III.定理11.4: a defect outside `I_Ob` gives a nonzero generated interpretation. -/
theorem interpret_ne_zero_of_defect_notMem_obstructionIdeal
    (D : LawEquationDefectSource E)
    (i : D.Chart)
    (hnot : D.defect i (D.input i) ∉ E.obstructionIdeal (D.chart i)) :
    D.interpret i ≠ 0 :=
  fun hzero => hnot ((D.interpret_eq_zero_iff_defect_mem_obstructionIdeal i).mp hzero)

/--
III.定理11.4: detector soundness.  A nonzero generated interpretation rules
out every displayed required law on that local reading.
-/
theorem interpret_ne_zero_detects_displayed_required_law_failure
    (D : LawEquationDefectSource E)
    (i : D.Chart)
    (hne : D.interpret i ≠ 0) :
    forall equationIndex : E.Index,
      equationIndex ∈ D.lawSupport i (D.input i) ->
        E.Required equationIndex ->
          ¬ E.EquationHolds equationIndex
              (D.objectOfLocalInput i (D.input i)) := by
  intro equationIndex hmem hrequired hholdsLaw
  refine hne ?_
  have hdefect :
      D.defect i (D.input i) ∈ E.witnessIdeal (D.chart i) equationIndex :=
    D.holds_defect_mem i equationIndex hmem hrequired hholdsLaw
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (E.witnessIdeal_le_obstructionIdeal (D.chart i) hrequired hdefect)

/-- III.定理11.4: displayed law fulfillment constructs pointwise interpretation zero. -/
theorem displayedRequiredLawsHoldOn_constructs_generatedInterpretationPointwiseZero
    (D : LawEquationDefectSource E)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    D.GeneratedInterpretationPointwiseZero :=
  D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds

/-- III.定理11.4 package: law-equation grounding for generated coefficients. -/
theorem lawEquation_grounding_packet
    (D : LawEquationDefectSource E)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    (forall i : D.Chart, D.interpret i = 0) /\
      D.GeneratedInterpretationPointwiseZero /\
      (forall i : D.Chart,
        D.interpret i = 0 <->
          D.defect i (D.input i) ∈ E.obstructionIdeal (D.chart i)) /\
      (forall i : D.Chart,
        D.interpret i ≠ 0 ->
          forall equationIndex : E.Index,
            equationIndex ∈ D.lawSupport i (D.input i) ->
              E.Required equationIndex ->
                ¬ E.EquationHolds equationIndex
                    (D.objectOfLocalInput i (D.input i))) :=
  ⟨D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds,
    D.displayedRequiredLawsHoldOn_constructs_generatedInterpretationPointwiseZero hholds,
    D.interpret_eq_zero_iff_defect_mem_obstructionIdeal,
    fun i hne =>
      D.interpret_ne_zero_detects_displayed_required_law_failure i hne⟩

end LawEquationDefectSource

end LawAlgebra
end AAT.AG
