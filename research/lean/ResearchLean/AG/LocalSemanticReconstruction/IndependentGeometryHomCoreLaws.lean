import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomTransportMatching
import Formal.Util.AssertStandardAxioms

/-!
# Core transport equations derived from common primitive Hom rows

The local conditions below refer to individual source/target extraction,
composition, and formation cells and to true Hom point pairs. Native whole
family, composition, formation, and configuration equations are consequences,
not fields of these conditions. No completed core Hom is stored.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLaws

noncomputable section

universe u v

open IndependentCorePrimitive

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Four primitive admission responses, evaluated at the selected reading parameters. -/
def admitted (t : Extraction.Table U) (S : Type u) (s : S) (a : U.Atom) : Prop :=
  (t (.vocabulary (Extraction.carrier t .vocabulary) (Extraction.point t .vocabulary) a)).down ∧
    (t (.semantic (Extraction.carrier t .semantic) S (Extraction.point t .semantic) s a)).down ∧
    (t (.resolution (Extraction.carrier t .resolution) S (Extraction.point t .resolution) s a)).down ∧
    (t (.source S s a)).down

/-- Assembled extraction is precisely the four primitive admission readings. -/
theorem admitted_iff (t : Extraction.Table U) (ht : Extraction.IsTyped t)
    (s : Extraction.carrier t .source) (a : U.Atom) :
    admitted t _ ((Extraction.doctrine t ht).normalize s) a ↔
      (Extraction.doctrine t ht).extracts s a := Iff.rfl

/-- Source transport laws use one selected source pair, normalization points, and admissions. -/
structure ExtractionLaws (s t : Extraction.Table U) (h : Table.{u, v} U mode) : Prop where
  /-- Source rows are exactly a directed total function at the declared carriers. -/
  source : IndependentCarrierGraph.IsLawful (Extraction.carrier s .source)
    (Extraction.carrier t .source) (IndependentGeometryHomPrimitive.source h)
  /-- The selected source pair has a true graph cell. -/
  selected : h (.source (.edge (Extraction.carrier s .source) (Extraction.carrier t .source)
    (Extraction.point s .source) (Extraction.point t .source))) = true
  /-- Normalization preserves each true source point pair. -/
  normalize : ∀ S T (x nx : S) (y ny : T),
    h (.source (.edge S T x y)) = true →
    (s (.normalize S x)).down = some nx → (t (.normalize T y)).down = some ny →
    h (.source (.edge S T nx ny)) = true
  /-- Each true pointed Atom/source pair has the same four-admission conjunction. -/
  extraction : ∀ S T (x nx : S) (y ny : T) a b,
    h (.source (.edge S T x y)) = true → h (.pointedAtom .forward a b) = true →
    (s (.normalize S x)).down = some nx → (t (.normalize T y)).down = some ny →
    (admitted s S nx a ↔ admitted t T ny b)

/-- Construct the directed source map from the common exact-one source rows. -/
def sourceMap (s t : Extraction.Table U) (h : Table.{u, v} U mode) (hl : ExtractionLaws s t h) :
    Extraction.carrier s .source → Extraction.carrier t .source :=
  IndependentCarrierGraph.assemble _ _ (IndependentGeometryHomPrimitive.source h) hl.source

/-- The native selected-source equation follows from its single true pair. -/
theorem source_eq (s t : Extraction.Table U) (h : Table.{u, v} U mode) (hl : ExtractionLaws s t h) :
    sourceMap s t h hl (Extraction.point s .source) = Extraction.point t .source :=
  IndependentCarrierGraph.assemble_eq_of_edge _ _ _ hl.source hl.selected

/-- Pointwise normalization clauses imply the original directed normalization equation. -/
theorem normalize_eq (s t : Extraction.Table U) (hs : Extraction.IsTyped s) (ht : Extraction.IsTyped t)
    (h : Table.{u, v} U mode) (hl : ExtractionLaws s t h) (x : Extraction.carrier s .source) :
    (Extraction.doctrine t ht).normalize (sourceMap s t h hl x) =
      sourceMap s t h hl ((Extraction.doctrine s hs).normalize x) := by
  have hx := IndependentCarrierGraph.edge_assemble _ _ _ hl.source x
  have hn := hl.normalize _ _ x ((Extraction.doctrine s hs).normalize x)
    (sourceMap s t h hl x) ((Extraction.doctrine t ht).normalize (sourceMap s t h hl x)) hx
    (Option.some_get _).symm (Option.some_get _).symm
  exact (IndependentCarrierGraph.assemble_eq_of_edge _ _ _ hl.source hn).symm

/-- Admission clauses yield the native pointed extraction equivalence at every source and Atom. -/
theorem extraction_iff (s t : Extraction.Table U) (hs : Extraction.IsTyped s) (ht : Extraction.IsTyped t)
    (h : Table.{u, v} U mode) (hl : ExtractionLaws s t h) (ha : Atom.IsCoherent h)
    (x : Extraction.carrier s .source) (a : U.Atom) :
    (Extraction.doctrine s hs).extracts x a ↔
      (Extraction.doctrine t ht).extracts (sourceMap s t h hl x)
        (Atom.assemble (Atom.pointed h) ha.pointed a) :=
  hl.extraction _ _ x _ _ _ a _ (IndependentCarrierGraph.edge_assemble _ _ _ hl.source x)
    (Atom.edge_assemble _ ha.pointed a) (Option.some_get _).symm (Option.some_get _).symm

/-- The native extracted-family transport equation is derived, including pointed/upper agreement. -/
theorem extracted_family_eq (s t : Extraction.Table U) (hs : Extraction.IsTyped s) (ht : Extraction.IsTyped t)
    (h : Table.{u, v} U mode) (hl : ExtractionLaws s t h) (ha : Atom.IsCoherent h) :
    Generation.family t ht = (Generation.family s hs).transport (TransportMatch.atomEquiv h ha.upper) := by
  apply TransportMatch.family_eq_of_points h ha.upper
  intro a b hab
  have he := (TransportMatch.edge_iff h ha.upper a b).1 hab
  have hp : Atom.assemble (Atom.pointed h) ha.pointed a = b := by
    rw [Atom.pointed_eq_upper h ha]
    exact he
  have hr := extraction_iff s t hs ht h hl ha (Extraction.point s .source) a
  rw [source_eq s t h hl, hp] at hr
  exact hr

/-- Object-map rows are directed total-function graphs, independently of any formed object. -/
def ObjectRows (h : Table.{u, v} U mode) : Prop :=
  ∀ A : ArchitectureObject U, ∃! B : ArchitectureObject U, h (.object A B) = true

/-- Collect the directed object graph without imposing injectivity or surjectivity. -/
def objectGraph (h : Table.{u, v} U mode) (hl : ObjectRows h) :
    PrimitiveFunctionGraph.GraphCode (ArchitectureObject U) (ArchitectureObject U) :=
  ⟨⟨fun A B => h (.object A B)⟩, ⟨hl⟩⟩

/-- Construct the native object map from its unique primitive point outputs. -/
def objectMap (h : Table.{u, v} U mode) (hl : ObjectRows h) :
    ArchitectureObject U → ArchitectureObject U := (objectGraph h hl).assemble

/-- An object candidate matches formation exactly when its configuration and two primitive values match. -/
def FormationMatch (t : ObjectFormation.Table U) (C : AtomConfiguration U) (A : ArchitectureObject U) : Prop :=
  A.configuration = C ∧
    (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u}) = t (.structureMaps C) ∧
    (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u}) = t (.selectedQuantities C)

/-- Formation matching is equivalent to equality with the object generated from the two point values. -/
theorem formationMatch_iff (t : ObjectFormation.Table U) (C : AtomConfiguration U) (A : ArchitectureObject U) :
    FormationMatch t C A ↔ A = ObjectFormation.object t C := by
  constructor
  · rintro ⟨hc, hs, hq⟩
    cases A with
    | mk conf SM SQ sm sq =>
      dsimp at hc hs hq
      subst conf
      exact congrArg₂ (fun (x y : SelectedValue.{u}) =>
        (⟨C, x.1, y.1, x.2, y.2⟩ : ArchitectureObject U)) hs hq
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

/-- Composition and formation preservation use only candidate references and primitive point values. -/
structure GenerationLaws (cs ct : Composition.Table U) (fs ft : ObjectFormation.Table U)
    (h : Table.{u, v} U mode) : Prop where
  /-- A true family match preserves each relation/identification pair at true Atom graph pairs. -/
  composition : ∀ F F' (hf : F.ListFinite) (hf' : F'.ListFinite) a a' b b',
    h (.familyTransport F F') = true →
    h (.atom .forward a a') = true → h (.atom .forward b b') = true →
    (cs (.relation F hf a b) ↔ ct (.relation F' hf' a' b')) ∧
      (cs (.identification F hf a b) ↔ ct (.identification F' hf' a' b'))
  /-- Matched configurations and formed primitive values must be related by the object graph. -/
  formation : ∀ C C' A B, h (.configurationTransport C C') = true →
    FormationMatch fs C A → FormationMatch ft C' B → h (.object A B) = true
  /-- Each true object graph pair preserves its configuration point readings. -/
  configuration : ∀ A B, h (.object A B) = true →
    h (.configurationTransport A.configuration B.configuration) = true

/-- Primitive composition comparisons derive the original whole configuration transport equation. -/
theorem composition_eq (cs ct : Composition.Table U) (hcs : Composition.IsLawful cs)
    (hct : Composition.IsLawful ct) (fs ft : ObjectFormation.Table U) (h : Table.{u, v} U mode)
    (ha : Atom.IsLawful (Atom.upper h)) (hm : TransportMatch.IsLawful h)
    (hl : GenerationLaws cs ct fs ft h) (F : AtomFamily U) (hf : F.ListFinite) :
    (Composition.assemble ct hct).compose (F.transport (TransportMatch.atomEquiv h ha))
        (hf.transport (TransportMatch.atomEquiv h ha)) =
      ((Composition.assemble cs hcs).compose F hf).transport (TransportMatch.atomEquiv h ha) := by
  apply TransportMatch.configuration_eq_of_points h ha
  · rfl
  · intro a a' b b' haa hbb
    exact hl.composition F _ hf _ a a' b b' ((TransportMatch.family_iff h ha hm _ _).2 rfl) haa hbb

/-- Candidate matching derives preservation of complete object formation after directed graph assembly. -/
theorem object_formation_eq (cs ct : Composition.Table U) (fs ft : ObjectFormation.Table U)
    (h : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper h)) (hm : TransportMatch.IsLawful h)
    (ho : ObjectRows h) (hl : GenerationLaws cs ct fs ft h) (C : AtomConfiguration U) :
    objectMap h ho (ObjectFormation.object fs C) =
      ObjectFormation.object ft (C.transport (TransportMatch.atomEquiv h ha)) := by
  apply (objectGraph h ho).target_eq_of_edge
  exact hl.formation C _ _ _ ((TransportMatch.configuration_iff h ha hm _ _).2 rfl)
    ((formationMatch_iff fs C _).2 rfl) ((formationMatch_iff ft _ _).2 rfl)

/-- Each reconstructed object image has exactly the native transported configuration. -/
theorem configuration_eq (cs ct : Composition.Table U) (fs ft : ObjectFormation.Table U)
    (h : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper h)) (hm : TransportMatch.IsLawful h)
    (ho : ObjectRows h) (hl : GenerationLaws cs ct fs ft h) (A : ArchitectureObject U) :
    (objectMap h ho A).configuration = A.configuration.transport (TransportMatch.atomEquiv h ha) :=
  (TransportMatch.configuration_iff h ha hm _ _).1
    (hl.configuration A _ ((objectGraph h ho).edge_target A))

/-- Every native normalization/extraction-preserving map satisfies the local point clauses. -/
theorem extractionLaws_of_native (s t : Extraction.Table U)
    (hs : Extraction.IsTyped s) (ht : Extraction.IsTyped t) (h : Table.{u, v} U mode)
    (hg : IndependentCarrierGraph.IsLawful (Extraction.carrier s .source)
      (Extraction.carrier t .source) (IndependentGeometryHomPrimitive.source h))
    (ha : Atom.IsLawful (Atom.pointed h))
    (hselected : IndependentCarrierGraph.assemble _ _ (IndependentGeometryHomPrimitive.source h) hg
      (Extraction.point s .source) = Extraction.point t .source)
    (hnormalize : ∀ x, (Extraction.doctrine t ht).normalize
      (IndependentCarrierGraph.assemble _ _ (IndependentGeometryHomPrimitive.source h) hg x) =
      IndependentCarrierGraph.assemble _ _ (IndependentGeometryHomPrimitive.source h) hg
        ((Extraction.doctrine s hs).normalize x))
    (hextraction : ∀ x a, (Extraction.doctrine s hs).extracts x a ↔
      (Extraction.doctrine t ht).extracts
        (IndependentCarrierGraph.assemble _ _ (IndependentGeometryHomPrimitive.source h) hg x)
        (Atom.assemble (Atom.pointed h) ha a)) : ExtractionLaws s t h := by
  have active : ∀ S T (x : S) (y : T), h (.source (.edge S T x y)) = true →
      S = Extraction.carrier s .source ∧ T = Extraction.carrier t .source := by
    intro S T x y he
    constructor
    · by_contra hn
      exact Bool.noConfusion ((hg.1 S T x y (Or.inl hn)).symm.trans he)
    · by_contra hn
      exact Bool.noConfusion ((hg.1 S T x y (Or.inr hn)).symm.trans he)
  refine ⟨hg, ?_, ?_, ?_⟩
  · rw [← hselected]
    exact IndependentCarrierGraph.edge_assemble _ _ _ hg _
  · intro S T x nx y ny hxy hnx hny
    obtain ⟨rfl, rfl⟩ := active S T x y hxy
    have hy := IndependentCarrierGraph.assemble_eq_of_edge _ _ _ hg hxy
    have hxN : (Extraction.doctrine s hs).normalize x = nx := by
      apply Option.some.inj
      exact (Option.some_get _).trans hnx
    have hyN : (Extraction.doctrine t ht).normalize y = ny := by
      apply Option.some.inj
      exact (Option.some_get _).trans hny
    have hn := (congrArg (IndependentCarrierGraph.assemble _ _
      (IndependentGeometryHomPrimitive.source h) hg) hxN).symm.trans
      ((hnormalize x).symm.trans ((congrArg (Extraction.doctrine t ht).normalize hy).trans hyN))
    rw [← hn]
    exact IndependentCarrierGraph.edge_assemble _ _ _ hg nx
  · intro S T x nx y ny a b hxy hab hnx hny
    obtain ⟨rfl, rfl⟩ := active S T x y hxy
    have hy := IndependentCarrierGraph.assemble_eq_of_edge _ _ _ hg hxy
    have hb := Atom.assemble_eq_of_edge (Atom.pointed h) ha hab
    have hxN : (Extraction.doctrine s hs).normalize x = nx := by
      apply Option.some.inj
      exact (Option.some_get _).trans hnx
    have hyN : (Extraction.doctrine t ht).normalize y = ny := by
      apply Option.some.inj
      exact (Option.some_get _).trans hny
    have hh := (hextraction x a).trans (Iff.of_eq
      (congrArg₂ (Extraction.doctrine t ht).extracts hy hb))
    have hn := (admitted_iff s hs x a).trans (hh.trans (admitted_iff t ht y b).symm)
    rw [hxN, hyN] at hn
    exact hn

/-- Native generation transport implies every guarded composition, formation, and configuration point rule. -/
theorem generationLaws_of_native (cs ct : Composition.Table U) (hcs : Composition.IsLawful cs)
    (hct : Composition.IsLawful ct) (fs ft : ObjectFormation.Table U)
    (h : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper h)) (hm : TransportMatch.IsLawful h)
    (ho : ObjectRows h)
    (hcompose : ∀ F hf, (Composition.assemble ct hct).compose
      (F.transport (TransportMatch.atomEquiv h ha)) (hf.transport (TransportMatch.atomEquiv h ha)) =
        ((Composition.assemble cs hcs).compose F hf).transport (TransportMatch.atomEquiv h ha))
    (hformation : ∀ C, objectMap h ho (ObjectFormation.object fs C) =
      ObjectFormation.object ft (C.transport (TransportMatch.atomEquiv h ha)))
    (hconfiguration : ∀ A, (objectMap h ho A).configuration =
      A.configuration.transport (TransportMatch.atomEquiv h ha)) : GenerationLaws cs ct fs ft h := by
  constructor
  · intro F F' hf hf' a a' b b' hF haa hbb
    have heF := (TransportMatch.family_iff h ha hm F F').1 hF
    have hea := (TransportMatch.edge_iff h ha a a').1 haa
    have heb := (TransportMatch.edge_iff h ha b b').1 hbb
    subst F'
    subst a'
    subst b'
    change (((Composition.assemble cs hcs).compose F hf).relation a b ↔
        ((Composition.assemble ct hct).compose _ hf').relation _ _) ∧
      (((Composition.assemble cs hcs).compose F hf).identification a b ↔
        ((Composition.assemble ct hct).compose _ hf').identification _ _)
    rw [hcompose F hf]
    exact ⟨(TransportMatch.relation_transport_image _ _ a b).symm,
      (TransportMatch.identification_transport_image _ _ a b).symm⟩
  · intro C C' A B hC hA hB
    have heC := (TransportMatch.configuration_iff h ha hm C C').1 hC
    have heA := (formationMatch_iff fs C A).1 hA
    have heB := (formationMatch_iff ft C' B).1 hB
    subst A
    subst B
    subst C'
    rw [← hformation C]
    exact (objectGraph h ho).edge_target _
  · intro A B hAB
    have heB : objectMap h ho A = B := (objectGraph h ho).target_eq_of_edge hAB
    apply (TransportMatch.configuration_iff h ha hm _ _).2
    rw [← heB]
    exact hconfiguration A

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLaws

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLaws
