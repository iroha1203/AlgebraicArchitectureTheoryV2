import ResearchLean.AG.GeometryTransport.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MvPolynomial.Variables
import Formal.Util.AssertStandardAxioms

/-!
# G-124 independent validation of dependent raw readings

This is an independent verification of the design recorded in tracking Issue
4711, comment 5742767034, sections 3 and 4.2. It is not a research cycle.

## Implementation notes

Queries name only the native raw roles: coordinate types, coordinate labels,
local-data types, relation indices, relation polynomials, and variable images.
Candidate types make the query type independent of a selected raw system.
An inactive candidate returns `none`. A table contains point values; neither
a raw system nor a completed restriction homomorphism is a table value.

The site and coefficient ring are parameters of this verification. Their
reconstruction from core readings remains a separate obligation of G-124.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRawLocal

noncomputable section

open CategoryTheory LawAlgebra

universe u v

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable (S : Site.AATSite A) (k : Type v) [CommRing k]

/-- Native raw query addresses, declared before choosing any raw system. -/
inductive Query where
  /-- Select the native coordinate carrier at a context. -/
  | coordinate (W : S.category)
  /-- Read one label at a candidate coordinate. -/
  | label (W : S.category) (C : Type u) (c : C)
  /-- Read the native local-data carrier at a candidate coordinate. -/
  | localData (W : S.category) (C : Type u) (c : C)
  /-- Select the native relation-index carrier at a context. -/
  | relation (W : S.category)
  /-- Read one finite relation polynomial using candidate carriers. -/
  | polynomial (W : S.category) (C R : Type u) (r : R)
  /-- Read the finite polynomial image of one target coordinate. -/
  | image {X Y : S.category} (f : X ⟶ Y) (C D : Type u) (d : D)

/-- Each response is one type reference, label, or finite polynomial. -/
def Query.Value : Query S → Type (max (u + 1) v)
  | .coordinate _ => ULift.{max (u + 1) v} (Type u)
  | .label _ _ _ => ULift.{max (u + 1) v} (Option CoordinateLabel)
  | .localData _ _ _ => ULift.{max (u + 1) v} (Option (Type u))
  | .relation _ => ULift.{max (u + 1) v} (Type u)
  | .polynomial _ C _ _ => ULift.{max (u + 1) v} (Option (MvPolynomial C k))
  | .image _ C _ _ => ULift.{max (u + 1) v} (Option (MvPolynomial C k))

/-- A family of primitive point responses with independently declared indices. -/
abbrev Table := (q : Query S) → Query.Value S k q

variable {S k}

/-- Selected coordinate type, obtained from one declared raw query. -/
abbrev coord (t : Table S k) (W : S.category) : Type u := (t (.coordinate W)).down

/-- Selected relation index type, obtained from one declared raw query. -/
abbrev rel (t : Table S k) (W : S.category) : Type u := (t (.relation W)).down

/-- Exact activation rules for dependent candidate queries. Inactive values
are forced to be `none` by the same biconditionals. -/
structure IsTyped (t : Table S k) : Prop where
  /-- A label response is active exactly at the selected coordinate carrier. -/
  label : ∀ W C c, (t (.label W C c)).down.isSome ↔ C = coord t W
  /-- A local-data carrier response has the same activation rule. -/
  localData : ∀ W C c, (t (.localData W C c)).down.isSome ↔ C = coord t W
  /-- Polynomial responses require both selected coordinate and relation carriers. -/
  polynomial : ∀ W C R r, (t (.polynomial W C R r)).down.isSome ↔
    C = coord t W ∧ R = rel t W
  /-- Variable images require the selected source and target coordinate carriers. -/
  image : ∀ {X Y} (f : X ⟶ Y) C D d,
    (t (.image f C D d)).down.isSome ↔ C = coord t X ∧ D = coord t Y

/-- Recover a coordinate family by selecting its active point responses. -/
abbrev coordinates (t : Table S k) (ht : IsTyped t) (W : S.category) :
    CoordinateFamily W.ctx where
  Coord := coord t W
  label c := (t (.label W (coord t W) c)).down.get ((ht.label _ _ _).2 rfl)
  LocalData c := (t (.localData W (coord t W) c)).down.get
    ((ht.localData _ _ _).2 rfl)

/-- Recover relation polynomials, after recovering their coordinate type. -/
def relations (t : Table S k) (ht : IsTyped t) (W : S.category) :
    StructuralRelationFamily (coordinates t ht W) k where
  Relation := rel t W
  polynomial r := (t (.polynomial W (coord t W) (rel t W) r)).down.get
    ((ht.polynomial _ _ _ _).2 ⟨rfl, rfl⟩)

/-- Recover the image of one variable; the polynomial map is generated later. -/
def variableImage (t : Table S k) (ht : IsTyped t)
    {X Y : S.category} (f : X ⟶ Y) (c : coord t Y) : MvPolynomial (coord t X) k :=
  (t (.image f (coord t X) (coord t Y) c)).down.get
    ((ht.image _ _ _ _).2 ⟨rfl, rfl⟩)

/-- The native restriction is constructed from the variable readings. -/
def restriction (t : Table S k) (ht : IsTyped t)
    {X Y : S.category} (f : X ⟶ Y) :
    TypedCoordinateRestriction (coordinates t ht X) (coordinates t ht Y) k
      (S.contextPreorder.morphism (leOfHom f)) where
  variableImage := variableImage t ht f

/-- Independent generator, identity, and composition equations for the table.
The finite ideal witness is a proposition, not an extra selected field. -/
structure IsLawful (t : Table S k) (ht : IsTyped t) : Prop where
  /-- Each transported generator is a finite polynomial combination of source relations. -/
  generator : ∀ {X Y} (f : X ⟶ Y) (r : rel t Y),
    ∃ w : rel t X →₀ MvPolynomial (coord t X) k,
      w.sum (fun i a => a * (relations t ht X).polynomial i) =
        (restriction t ht f).polynomialMap ((relations t ht Y).polynomial r)
  /-- The native identity law is imposed only on each variable. -/
  identity : ∀ W (c : coord t W), variableImage t ht (𝟙 W) c = MvPolynomial.X c
  /-- The native composition law is imposed only on each variable. -/
  composition : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (c : coord t Z),
    variableImage t ht (f ≫ g) c =
      (restriction t ht f).polynomialMap (variableImage t ht g c)

/-- Generate ideal preservation from the finite witness for each generator. -/
theorem maps_ideal (t : Table S k) (ht : IsTyped t) (hl : IsLawful t ht)
    {X Y : S.category} (f : X ⟶ Y) (p : MvPolynomial (coord t Y) k)
    (hp : p ∈ (relations t ht Y).JStruct) :
    (restriction t ht f).polynomialMap p ∈ (relations t ht X).JStruct := by
  have gen : ∀ r, (restriction t ht f).polynomialMap
      ((relations t ht Y).polynomial r) ∈ (relations t ht X).JStruct := by
    intro r
    change _ ∈ Submodule.span (MvPolynomial (coord t X) k)
      (Set.range (relations t ht X).polynomial)
    rw [Finsupp.mem_span_range_iff_exists_finsupp]
    exact hl.generator f r
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · rintro p ⟨r, rfl⟩
    exact gen r
  · simp
  · intro p q _ _ hp hq
    simpa using (relations t ht X).JStruct.add_mem hp hq
  · intro a p _ hp
    simpa using (relations t ht X).JStruct.mul_mem_left
      ((restriction t ht f).polynomialMap a) hp

/-- Assemble a native raw system from primitive table equations. -/
def assemble (t : Table S k) (ht : IsTyped t) (hl : IsLawful t ht) :
    RawAmbientRestrictionSystem S k where
  coordFamily := coordinates t ht
  relationFamily := relations t ht
  restrictionStable f := ⟨restriction t ht f, maps_ideal t ht hl f⟩
  identity_polynomialMap W := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [restriction, TypedCoordinateRestriction.polynomialMap]
    · intro c
      simpa [restriction, TypedCoordinateRestriction.polynomialMap] using hl.identity W c
  composition_polynomialMap f g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [restriction, TypedCoordinateRestriction.polynomialMap]
    · intro c
      simpa [restriction, TypedCoordinateRestriction.polynomialMap] using hl.composition f g c

/-- Pointwise raw reading, with canonical inactive responses for other types. -/
def read (B : RawAmbientRestrictionSystem S k) : Table S k := by
  classical
  intro q
  cases q with
  | coordinate W => exact ⟨(B.coordFamily W).Coord⟩
  | relation W => exact ⟨(B.relationFamily W).Relation⟩
  | label W C c =>
    exact ⟨if h : C = (B.coordFamily W).Coord then
      some ((B.coordFamily W).label (h ▸ c)) else none⟩
  | localData W C c =>
    exact ⟨if h : C = (B.coordFamily W).Coord then
      some ((B.coordFamily W).LocalData (h ▸ c)) else none⟩
  | polynomial W C R r =>
    exact ⟨if hC : C = (B.coordFamily W).Coord then
      if hR : R = (B.relationFamily W).Relation then
        some (hC.symm ▸ (B.relationFamily W).polynomial (hR ▸ r)) else none
      else none⟩
  | @image X Y f C D d =>
    exact ⟨if hC : C = (B.coordFamily X).Coord then
      if hD : D = (B.coordFamily Y).Coord then
        some (hC.symm ▸ (B.restrictionStable f).restriction.variableImage (cast hD d))
      else none else none⟩

/-- Every native raw system satisfies the candidate activation rules. -/
theorem read_isTyped (B : RawAmbientRestrictionSystem S k) : IsTyped (read B) := by
  classical
  constructor
  · intro W C c
    by_cases h : C = (B.coordFamily W).Coord <;> simp [read, coord, h]
  · intro W C c
    by_cases h : C = (B.coordFamily W).Coord <;> simp [read, coord, h]
  · intro W C R r
    by_cases hC : C = (B.coordFamily W).Coord <;>
      by_cases hR : R = (B.relationFamily W).Relation <;> simp [read, coord, rel, hC, hR]
  · intro X Y f C D d
    by_cases hC : C = (B.coordFamily X).Coord <;>
      by_cases hD : D = (B.coordFamily Y).Coord <;> simp [read, coord, hC, hD]

/-- The coordinate constructor recovers all three native fields. -/
@[simp] theorem coordinates_read (B : RawAmbientRestrictionSystem S k) (W : S.category) :
    coordinates (read B) (read_isTyped B) W = B.coordFamily W := by
  simp [coordinates, coord, read]

/-- Dependent extensionality for relation presentations over equal coordinate families. -/
theorem relation_heq_of_points {W : S.category}
    {F G : CoordinateFamily W.ctx} (hF : F = G)
    (R : StructuralRelationFamily F k) (T : StructuralRelationFamily G k)
    (hR : R.Relation = T.Relation) (hp : HEq R.polynomial T.polynomial) : HEq R T := by
  cases hF
  cases R
  cases T
  cases hR
  cases hp
  rfl

/-- Relation reconstruction retains the native index type and polynomial values. -/
theorem relations_read (B : RawAmbientRestrictionSystem S k) (W : S.category) :
    HEq (relations (read B) (read_isTyped B) W) (B.relationFamily W) := by
  apply relation_heq_of_points (coordinates_read B W)
  · rfl
  · apply heq_of_eq
    funext r
    simp [relations, coord, rel, read]

/-- Variable-image reconstruction recovers each native point evaluation. -/
@[simp] theorem variableImage_read (B : RawAmbientRestrictionSystem S k)
    {X Y : S.category} (f : X ⟶ Y) (c : (B.coordFamily Y).Coord) :
    variableImage (read B) (read_isTyped B) f c =
      (B.restrictionStable f).restriction.variableImage c := by
  simp [variableImage, coord, read]

/-- Function-level API for the variable-image reader, oriented toward native data. -/
@[simp] theorem variableImage_read_function (B : RawAmbientRestrictionSystem S k)
    {X Y : S.category} (f : X ⟶ Y) :
    variableImage (read B) (read_isTyped B) f =
      (B.restrictionStable f).restriction.variableImage :=
  funext (variableImage_read B f)

/-- Generator membership in an ideal has a finite polynomial-sum witness. -/
theorem mem_JStruct_iff_finite_sum {W : S.category}
    {F : CoordinateFamily W.ctx} (R : StructuralRelationFamily F k)
    (p : FreeTypedCommAlg F k) :
    p ∈ R.JStruct ↔ ∃ w : R.Relation →₀ FreeTypedCommAlg F k,
      w.sum (fun i a => a * R.polynomial i) = p := by
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- Native raw axioms imply exactly the local generator/id/composition rules. -/
theorem read_isLawful (B : RawAmbientRestrictionSystem S k) :
    IsLawful (read B) (read_isTyped B) := by
  constructor
  · intro X Y f r
    have hp := (B.restrictionStable f).maps_JStruct _
      ((B.relationFamily Y).polynomial_mem_JStruct r)
    obtain ⟨w, hw⟩ := (mem_JStruct_iff_finite_sum (B.relationFamily X) _).mp hp
    refine ⟨w, ?_⟩
    simpa [relations, restriction, coordinates, coord, rel, read,
      TypedCoordinateRestriction.polynomialMap] using hw
  · intro W c
    have h := RingHom.congr_fun (B.identity_polynomialMap W) (MvPolynomial.X c)
    simpa [variableImage_read, TypedCoordinateRestriction.polynomialMap_X] using h
  · intro X Y Z f g c
    have h := RingHom.congr_fun (B.composition_polynomialMap f g) (MvPolynomial.X c)
    simpa [restriction, coord, read, TypedCoordinateRestriction.polynomialMap]
      using h

/-- Dependent extensionality for stable restrictions, retaining both presentations. -/
theorem stable_heq_of_points {X Y : S.category} (f : X ⟶ Y)
    {FX GX : CoordinateFamily X.ctx} {FY GY : CoordinateFamily Y.ctx}
    (hX : FX = GX) (hY : FY = GY)
    {RX : StructuralRelationFamily FX k} {TX : StructuralRelationFamily GX k}
    {RY : StructuralRelationFamily FY k} {TY : StructuralRelationFamily GY k}
    (hRX : HEq RX TX) (hRY : HEq RY TY)
    (a : RestrictionStableStructuralRelations RX RY (S.contextPreorder.morphism (leOfHom f)))
    (b : RestrictionStableStructuralRelations TX TY (S.contextPreorder.morphism (leOfHom f)))
    (hv : HEq a.restriction.variableImage b.restriction.variableImage) : HEq a b := by
  cases hX
  cases hY
  cases hRX
  cases hRY
  cases a with
  | mk ar ap =>
    cases b with
    | mk br bp =>
      cases ar
      cases br
      cases hv
      rfl

/-- Every native raw system is recovered, including dependent presentations
and restriction data. The site and coefficient ring are unchanged parameters. -/
theorem assemble_read (B : RawAmbientRestrictionSystem S k) :
    assemble (read B) (read_isTyped B) (read_isLawful B) = B := by
  apply RawAmbientRestrictionSystem.ext
  · funext W
    exact coordinates_read B W
  · exact Function.hfunext rfl (by
      intro W W' h
      cases h
      exact relations_read B W)
  · apply Function.hfunext rfl
    intro X X' hx
    cases hx
    apply Function.hfunext rfl
    intro Y Y' hy
    cases hy
    apply Function.hfunext rfl
    intro f f' hf
    cases hf
    apply stable_heq_of_points f (coordinates_read B X) (coordinates_read B Y)
      (relations_read B X) (relations_read B Y)
    exact heq_of_eq (variableImage_read_function B f)

/-- An inactive optional response has exactly one representation. -/
theorem option_eq_none_of_inactive {α : Type*} {o : Option α} (h : ¬ o.isSome) :
    o = none := by
  cases o <;> simp_all

/-- Reading an assembled raw system recovers active and inactive responses alike. -/
theorem read_assemble (t : Table S k) (ht : IsTyped t) (hl : IsLawful t ht) :
    read (assemble t ht hl) = t := by
  classical
  funext q
  cases q with
  | coordinate W => rfl
  | relation W => rfl
  | label W C c =>
    apply ULift.ext
    by_cases hC : C = coord t W
    · subst C
      simp [read, assemble, coordinates, coord, Option.some_get]
    · have hn := option_eq_none_of_inactive (mt (ht.label W C c).1 hC)
      simp [read, assemble, coordinates, hC, hn]
  | localData W C c =>
    apply ULift.ext
    by_cases hC : C = coord t W
    · subst C
      simp [read, assemble, coordinates, coord, Option.some_get]
    · have hn := option_eq_none_of_inactive (mt (ht.localData W C c).1 hC)
      simp [read, assemble, coordinates, hC, hn]
  | polynomial W C R r =>
    apply ULift.ext
    by_cases hC : C = coord t W
    · subst C
      by_cases hR : R = rel t W
      · subst R
        simp [read, assemble, relations, coordinates, coord, rel, Option.some_get]
      · have hn := option_eq_none_of_inactive
          (fun h => hR ((ht.polynomial W (coord t W) R r).1 h).2)
        simp [read, assemble, relations, coordinates, hR, hn]
    · have hn := option_eq_none_of_inactive
        (fun h => hC ((ht.polynomial W C R r).1 h).1)
      simp [read, assemble, relations, coordinates, hC, hn]
  | @image X Y f C D d =>
    apply ULift.ext
    by_cases hC : C = coord t X
    · subst C
      by_cases hD : D = coord t Y
      · subst D
        simp [read, assemble, restriction, variableImage, coordinates, coord, Option.some_get]
      · have hn := option_eq_none_of_inactive
          (fun h => hD ((ht.image f (coord t X) D d).1 h).2)
        simp [read, assemble, coordinates, hD, hn]
    · have hn := option_eq_none_of_inactive
        (fun h => hC ((ht.image f C D d).1 h).1)
      simp [read, assemble, coordinates, hC, hn]

/-- Independently lawful primitive tables for a fixed site and coefficient ring. -/
abbrev LawfulTable (S : Site.AATSite A) (k : Type v) [CommRing k] :=
  {t : Table S k // ∃ ht : IsTyped t, IsLawful t ht}

/-- Raw objects correspond bijectively to independently lawful primitive tables. -/
def rawTableEquiv : RawAmbientRestrictionSystem S k ≃ LawfulTable S k where
  toFun B := ⟨read B, read_isTyped B, read_isLawful B⟩
  invFun t := assemble t.val t.property.choose t.property.choose_spec
  left_inv B := assemble_read B
  right_inv t := Subtype.ext (read_assemble t.val t.property.choose t.property.choose_spec)

/-- All primitive point readings separate complete native raw systems. -/
theorem read_injective : Function.Injective (read (S := S) (k := k)) := by
  intro B C h
  apply (rawTableEquiv (S := S) (k := k)).injective
  exact Subtype.ext h

/-- Point equations derive the strict raw transport equality required by G-122. -/
theorem raw_transport_eq_iff_points
    {G H : GeometryTransport.GeometryPackage.{u, v} U}
    (f : AtomFoundation.PackageTotalHom G.core H.core)
    (h : G.Coefficient →+* H.Coefficient) :
    H.raw = GeometryTransport.rawTransport f h ↔
      ∀ q, read H.raw q = read (GeometryTransport.rawTransport f h) q := by
  constructor
  · intro heq q
    rw [heq]
  · intro hq
    exact read_injective (funext hq)

/-- Restriction of one polynomial depends only on its finite set of variables. -/
theorem polynomialMap_eq_of_vars
    {X Y : S.category} {F : CoordinateFamily X.ctx} {G : CoordinateFamily Y.ctx}
    {f : Site.ContextMorphism X.ctx Y.ctx}
    (a b : TypedCoordinateRestriction F G k f) (p : FreeTypedCommAlg G k)
    (h : ∀ c ∈ p.vars, a.variableImage c = b.variableImage c) :
    a.polynomialMap p = b.polynomialMap p :=
  MvPolynomial.eval₂Hom_congr' rfl (fun c hc _ => h c hc) rfl

/-- One finite fragment is a finite dependent tuple of primitive responses. -/
abbrev Fragment (d : Finset (Query S)) := (q : d) → Query.Value S k q.val

/-- A family of all finite fragments; its address type is independent of a raw object. -/
abbrev FragmentFamily (S : Site.AATSite A) (k : Type v) [CommRing k] :=
  (d : Finset (Query S)) → Fragment (k := k) d

/-- Each fragment really has a finite set of queried addresses. -/
theorem fragment_addresses_finite (d : Finset (Query S)) : Finite d := inferInstance

/-- Restrict a point table to each finite set of queries. -/
def fragments (t : Table S k) : FragmentFamily S k := fun _ q => t q.val

/-- Finite-fragment compatibility only compares shared primitive responses. -/
def Compatible (m : FragmentFamily S k) : Prop :=
  ∀ (d e : Finset (Query S)) (h : d ⊆ e) (q : d), m d q = m e ⟨q.val, h q.property⟩

/-- Singleton readings recover one point table from a compatible family. -/
def glue (m : FragmentFamily S k) : Table S k := by
  classical
  exact fun q => m {q} ⟨q, by simp⟩

/-- Restrictions of any point table agree on overlaps. -/
theorem fragments_compatible (t : Table S k) : Compatible (fragments t) :=
  fun _ _ _ _ => rfl

/-- Reading singleton fragments is left inverse to finite restriction. -/
@[simp] theorem glue_fragments (t : Table S k) : glue (fragments t) = t := rfl

/-- Compatibility recovers every finite fragment from singleton readings. -/
theorem fragments_glue (m : FragmentFamily S k) (hm : Compatible m) :
    fragments (glue m) = m := by
  classical
  funext d q
  exact hm {q.val} d (Finset.singleton_subset_iff.mpr q.property) ⟨q.val, by simp⟩

/-- Locally lawful finite families add only the point typing and polynomial equations. -/
abbrev LocalRaw (S : Site.AATSite A) (k : Type v) [CommRing k] :=
  {m : FragmentFamily S k // Compatible m ∧ ∃ ht : IsTyped (glue m), IsLawful (glue m) ht}

/-- Assemble a raw object from its independent finite family. -/
def assembleFragments (m : LocalRaw S k) : RawAmbientRestrictionSystem S k :=
  assemble (glue m.val) m.property.2.choose m.property.2.choose_spec

/-- The raw object equivalence comes from singleton gluing and the primitive assembler. -/
def rawLocalEquiv : RawAmbientRestrictionSystem S k ≃ LocalRaw S k where
  toFun B := ⟨fragments (read B), fragments_compatible _, read_isTyped B, read_isLawful B⟩
  invFun := assembleFragments
  left_inv B := assemble_read B
  right_inv m := by
    apply Subtype.ext
    change fragments (read (assemble (glue m.val) _ _)) = m.val
    rw [read_assemble]
    exact fragments_glue m.val m.property.1

/-- Erasing labels leaves all type selectors intact and removes required point values. -/
def eraseLabels (t : Table S k) : Table S k := fun q =>
  match q with
  | .label _ _ _ => ⟨none⟩
  | q => t q

/-- A missing active label is rejected even though its finite restrictions agree. -/
theorem eraseLabels_not_typed (t : Table S k) (W : S.category) (c : coord t W) :
    ¬ IsTyped (eraseLabels t) := by
  intro h
  have hh := (h.label W (coord t W) c).2 rfl
  simp [eraseLabels] at hh

/-- A concrete raw object with one coordinate and the genuine relation X=0. -/
def unitRaw (S : Site.AATSite A) (k : Type v) [CommRing k] :
    RawAmbientRestrictionSystem S k where
  coordFamily _ := ⟨PUnit.{u + 1}, fun _ => .state, fun _ => PUnit.{u + 1}⟩
  relationFamily _ := ⟨PUnit.{u + 1}, fun _ => MvPolynomial.X PUnit.unit⟩
  restrictionStable _ := {
    restriction := ⟨MvPolynomial.X⟩
    maps_JStruct := by
      intro p hp
      simpa [TypedCoordinateRestriction.polynomialMap] using hp
  }
  identity_polynomialMap _ := by
    ext <;> simp [TypedCoordinateRestriction.polynomialMap]
  composition_polynomialMap _ _ := by
    ext <;> simp [TypedCoordinateRestriction.polynomialMap]

/-- Positive/negative typing witnesses on the same site and one-coordinate input. -/
theorem unitRaw_typing_witness (W : S.category) :
    IsTyped (read (unitRaw S k)) ∧ ¬ IsTyped (eraseLabels (read (unitRaw S k))) :=
  ⟨read_isTyped _, eraseLabels_not_typed _ W PUnit.unit⟩

/-- Replace every active variable image by 1, retaining the candidate activation pattern. -/
def replaceImages (t : Table S k) : Table S k := fun q =>
  match q with
  | .image f C D d => ⟨(t (.image f C D d)).down.map (fun _ => 1)⟩
  | q => t q

/-- Variable-image corruption cannot be detected by typing alone. -/
theorem replaceImages_isTyped (t : Table S k) (ht : IsTyped t) :
    IsTyped (replaceImages t) := by
  constructor
  · intro W C c
    exact ht.label W C c
  · intro W C c
    exact ht.localData W C c
  · intro W C R r
    exact ht.polynomial W C R r
  · intro X Y f C D d
    simpa [replaceImages, coord] using ht.image f C D d

/-- The corrupted variable-image table evaluates to the constant polynomial 1. -/
@[simp] theorem variableImage_replaceImages (t : Table S k) (ht : IsTyped t)
    {X Y : S.category} (f : X ⟶ Y) (c : coord t Y) :
    variableImage (replaceImages t) (replaceImages_isTyped t ht) f c = 1 := by
  have h := (ht.image f (coord t X) (coord t Y) c).2 ⟨rfl, rfl⟩
  cases ho : (t (.image f (coord t X) (coord t Y) c)).down with
  | none => simp [ho] at h
  | some p => simp [variableImage, replaceImages, coord, ho]

/-- The generator law rejects the map X↦1 for the relation X=0 over the integers. -/
theorem replaceImages_not_lawful (W : S.category) :
    ¬ IsLawful (replaceImages (read (unitRaw S ℤ)))
      (replaceImages_isTyped _ (read_isTyped _)) := by
  intro h
  obtain ⟨w, hw⟩ := h.generator (𝟙 W) PUnit.unit
  have hc := congrArg MvPolynomial.constantCoeff hw
  simp [relations, replaceImages, read, rel, coord, unitRaw, restriction,
    TypedCoordinateRestriction.polynomialMap, Finsupp.sum] at hc
  rw [variableImage_replaceImages _ (read_isTyped _)] at hc
  norm_num at hc

/-- Positive and negative raw-law instances use the same nonzero coefficient ring. -/
theorem unitRaw_law_witness (W : S.category) :
    IsLawful (read (unitRaw S ℤ)) (read_isTyped _) ∧
      ¬ IsLawful (replaceImages (read (unitRaw S ℤ)))
        (replaceImages_isTyped _ (read_isTyped _)) :=
  ⟨read_isLawful _, replaceImages_not_lawful W⟩

/-- A deliberately inconsistent family changes active labels in larger fragments. -/
def inconsistentFragments (t : Table S k) : FragmentFamily S k := by
  classical
  exact fun d => if d.card = 1 then fragments t d else fragments (eraseLabels t) d

/-- Singleton agreement is actually enforced when a label and its type appear together. -/
theorem inconsistentFragments_not_compatible (W : S.category) :
    ¬ Compatible (inconsistentFragments (read (unitRaw S ℤ))) := by
  classical
  intro h
  let q : Query S := .label W PUnit.{u + 1} PUnit.unit
  let c : Query S := .coordinate W
  have hc := h {q} {q, c} (by simp) ⟨q, by simp⟩
  have hd := congrArg (fun x : Query.Value S ℤ q => x.down) hc
  have hne : q ≠ c := by simp [q, c]
  simp [inconsistentFragments, fragments, q, c, eraseLabels, read, unitRaw,
    hne] at hd

end

end AAT.AG.LocalSemanticReconstruction.IndependentRawLocal

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRawLocal
