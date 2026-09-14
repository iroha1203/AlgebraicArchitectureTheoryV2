import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Finite.Card
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction

/-!
# Finite protocol presentations and their decoder

This module constructs the finite syntax `P_proto` from G-123(A,E), n1015 §3.
An object contains only vertex cardinalities, named-edge tables, observation
values, and proofs of the fixed path/observation equations.  A morphism contains
only vertex tables satisfying named-edge and observation equations.  The
decoder constructs the action of every quotient execution.

## Implementation notes

The syntax never stores a completed functor, natural transformation, or map on
all paths.  Mathlib's free-path lift and quotient lift construct those data.
The decoder is compared with the independent semantic category by explicit
restriction and extension maps before fullness and faithfulness are proved.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A finite protocol presentation over fixed `Q,L,O`.

This is the object syntax of G-123(A,E), n1015 §3.1.  Its data are exactly
finite state counts, named-operation tables, and state observations; the two
fields are the fixed relation and observation well-formedness premises. -/
structure ProtocolPresentation (S : ProtocolSchema.{u})
    (O : S.ExecutionCategory ⥤ Type u) where
  /-- Number of states at each fixed schema vertex. -/
  card : S.Vertex → ℕ
  /-- Finite transition table for each named schema operation. -/
  edgeTable : ∀ {v w : S.Vertex}, S.Edge v w → Fin (card v) → Fin (card w)
  /-- The named-edge tables satisfy each fixed generating path equation in `L`. -/
  relation_compatibility : ∀ r : S.RelationIndex,
    S.evaluatePath (A := fun v => Fin (card v)) edgeTable (S.relationLeft r) =
      S.evaluatePath (A := fun v => Fin (card v)) edgeTable (S.relationRight r)
  /-- Observation value attached to each displayed finite state. -/
  observationValue : ∀ v : S.Vertex, Fin (card v) → O.obj (S.vertexObject v)
  /-- Observations commute with each named operation, as required by n1015 §3.1. -/
  observation_edge : ∀ {v w : S.Vertex} (e : S.Edge v w),
    observationValue w ∘ edgeTable e =
      O.map (S.edgeMorphism e) ∘ observationValue v

namespace ProtocolPresentation

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}

/-- A finite presentation morphism is a vertex-table family satisfying the
named-edge and observation equations of G-123(B0), n1015 §3.1.  No completed
natural transformation or all-path certificate is stored. -/
@[ext]
structure Hom (P Q : ProtocolPresentation S O) where
  /-- Finite table at each fixed schema vertex. -/
  component : ∀ v : S.Vertex, Fin (P.card v) → Fin (Q.card v)
  /-- Commutation with each named operation generator. -/
  edge_naturality : ∀ {v w : S.Vertex} (e : S.Edge v w),
    component w ∘ P.edgeTable e = Q.edgeTable e ∘ component v
  /-- Preservation of the displayed observation at every vertex. -/
  observation_naturality : ∀ v : S.Vertex,
    Q.observationValue v ∘ component v = P.observationValue v

/-- Pointwise composition API for finite protocol morphisms.

The two generator equations compose without constructing or consulting a
completed semantic natural transformation. -/
def Hom.comp {P Q R : ProtocolPresentation S O} (a : Hom P Q) (b : Hom Q R) : Hom P R where
  component v := b.component v ∘ a.component v
  edge_naturality := fun {v w} e => by
    funext x
    calc
      b.component w (a.component w (P.edgeTable e x)) =
          b.component w (Q.edgeTable e (a.component v x)) :=
        congrArg (b.component w) (congrFun (a.edge_naturality e) x)
      _ = R.edgeTable e (b.component v (a.component v x)) :=
        congrFun (b.edge_naturality e) (a.component v x)
  observation_naturality := fun v => by
    funext x
    calc
      R.observationValue v (b.component v (a.component v x)) =
          Q.observationValue v (a.component v x) :=
        congrFun (b.observation_naturality v) (a.component v x)
      _ = P.observationValue v x := congrFun (a.observation_naturality v) x

/-- Finite protocol presentations form the syntax category of G-123(A,E).

Identity and composition are pointwise on the vertex tables, so the category
still contains all noninvertible generator maps satisfying the fixed equations. -/
instance : Category (ProtocolPresentation S O) where
  Hom := Hom
  id P :=
    { component := fun _ => id
      edge_naturality := fun _ => rfl
      observation_naturality := fun _ => rfl }
  comp := Hom.comp
  id_comp := by
    intro P Q a
    ext v x
    rfl
  comp_id := by
    intro P Q a
    ext v x
    rfl
  assoc := by
    intro P Q R T a b c
    ext v x
    rfl

/-- Generator-map data of the finite syntax.

This is the codomain of `J` in G-123(B0); because presentation morphisms are
literally finite vertex tables with the required generator equations, it is
definitionally the same data as `Hom`. -/
abbrev GeneratorMap (P Q : ProtocolPresentation S O) := Hom P Q

/-- Syntax evaluation `J` is a bijection onto the finite generator-map data.

The identity equivalence is nonvacuous here: completed path naturality is not a
field of either side and is constructed later by the decoder. -/
def evaluationEquiv (P Q : ProtocolPresentation S O) :
    (P ⟶ Q) ≃ GeneratorMap P Q :=
  Equiv.refl _

/-- The free-path functor generated from a protocol presentation's edge tables.

This is decoder construction API for n1015 §3.1; composite executions are
constructed by `Paths.lift`, not supplied in the presentation. -/
def pathFunctor (P : ProtocolPresentation S O) : Paths S.Vertex ⥤ Type u :=
  S.pathFunctorOfEdgeAction (fun v => ULift.{u} (Fin (P.card v)))
    (fun e k => ULift.up (P.edgeTable e k.down))

/-- The universe-lifted decoder path action has exactly the original finite
table evaluation after lowering.  This no-unfold API preserves every execution
value while placing the decoder in `Type u`. -/
@[simp]
theorem pathFunctor_map_down (P : ProtocolPresentation S O)
    {v w : S.Vertex} (p : Quiver.Path v w)
    (k : ULift.{u} (Fin (P.card v))) :
    (P.pathFunctor.map p k).down = S.evaluatePath P.edgeTable p k.down :=
  S.evaluatePath_ulift P.edgeTable p k

/-- The path-table action respects the fixed generating relation family `L`.

This API theorem converts the presentation premise into the equality required
by Mathlib's quotient lift. -/
theorem pathFunctor_relation (P : ProtocolPresentation S O)
    {v w : Paths S.Vertex} (p q : v ⟶ w) (h : S.pathRelation p q) :
    P.pathFunctor.map p = P.pathFunctor.map q := by
  obtain ⟨r, hs, ht, hp, hq⟩ := h
  cases hs
  cases ht
  subst p
  subst q
  funext k
  apply ULift.down_injective
  rw [P.pathFunctor_map_down, P.pathFunctor_map_down]
  exact congrFun (P.relation_compatibility r) k.down

/-- The functor on the quotient execution category decoded from finite tables.

This is the semantic object map of G-123(E); path actions and relation descent
are constructed from `edgeTable` and `relation_compatibility`. -/
def decodedFunctor (P : ProtocolPresentation S O) : S.ExecutionCategory ⥤ Type u :=
  CategoryTheory.Quotient.lift S.pathRelation P.pathFunctor
    (fun _ _ p q h => P.pathFunctor_relation p q h)

/-- The displayed observations form a natural transformation on free paths.

This path-induction API constructs all-execution observation compatibility from
the named-edge equations in the presentation. -/
def pathObservation (P : ProtocolPresentation S O) :
    P.pathFunctor ⟶ CategoryTheory.Quotient.functor S.pathRelation ⋙ O :=
  Paths.liftNatTrans (fun v k => P.observationValue v k.down) (fun e => by
    funext k
    exact congrFun (P.observation_edge e) k.down)

/-- The observation map decoded on the quotient execution category.

Naturality for every quotient morphism is constructed by quotient induction
from `pathObservation`; it is not a presentation field. -/
def decodedObservation (P : ProtocolPresentation S O) : P.decodedFunctor ⟶ O where
  app q := fun k => P.observationValue q.as k.down
  naturality := by
    intro q q' f
    apply CategoryTheory.Quotient.induction (r := S.pathRelation)
      (P := fun {a b} f =>
        P.decodedFunctor.map f ≫ (fun k => P.observationValue b.as k.down) =
          (fun k => P.observationValue a.as k.down) ≫ O.map f)
    intro a b p
    exact P.pathObservation.naturality p

/-- Decode a finite presentation as an object of the independent protocol
semantic category.  Finiteness is derived from the `Fin` carriers. -/
def decoderObject (P : ProtocolPresentation S O) : ProtocolRealization S O where
  toFunctor := P.decodedFunctor
  state_finite := fun v => by
    change Finite (ULift.{u} (Fin (P.card v)))
    infer_instance
  observation := P.decodedObservation

/-- Generator squares of a syntax morphism extend along every free path.

This is the path-inductive proof used to construct the decoder on morphisms. -/
def homPathNatTrans {P Q : ProtocolPresentation S O} (a : P ⟶ Q) :
    P.pathFunctor ⟶ Q.pathFunctor :=
  Paths.liftNatTrans (fun v k => ULift.up (a.component v k.down)) (fun e => by
    funext k
    apply ULift.down_injective
    exact congrFun (a.edge_naturality e) k.down)

/-- Decode a finite syntax morphism as a complete natural transformation over
the observation functor.  Naturality on quotient executions is constructed,
not stored in `a`. -/
def decoderMap {P Q : ProtocolPresentation S O} (a : P ⟶ Q) :
    decoderObject P ⟶ decoderObject Q where
  toNatTrans :=
    { app := fun q k => ULift.up (a.component q.as k.down)
      naturality := by
        intro q q' f
        apply CategoryTheory.Quotient.induction (r := S.pathRelation)
          (P := fun {x y} f =>
            P.decodedFunctor.map f ≫ (fun k => ULift.up (a.component y.as k.down)) =
              (fun k => ULift.up (a.component x.as k.down)) ≫ Q.decodedFunctor.map f)
        intro x y p
        exact (ProtocolPresentation.homPathNatTrans a).naturality p }
  observation_naturality := by
    ext q x
    exact congrFun (a.observation_naturality q.as) x.down

/-- The finite protocol decoder functor of G-123(E), n1015 §3.1.

Its object and morphism maps are constructed solely from the finite syntax and
the fixed schema/observation parameters. -/
def decoder (S : ProtocolSchema.{u}) (O : S.ExecutionCategory ⥤ Type u) :
    ProtocolPresentation S O ⥤ ProtocolRealization S O where
  obj := decoderObject
  map := decoderMap
  map_id P := by
    apply ProtocolRealization.Hom.ext
    ext q x
    rfl
  map_comp a b := by
    apply ProtocolRealization.Hom.ext
    ext q x
    rfl

/-- Restrict a complete morphism between decoded objects to its finite vertex
tables.  This is the displayed `res` of G-123(B0). -/
def displayedRes {P Q : ProtocolPresentation S O}
    (a : (decoder S O).obj P ⟶ (decoder S O).obj Q) : P ⟶ Q where
  component v k := (a.toNatTrans.app (S.vertexObject v) (ULift.up k)).down
  edge_naturality := fun e => by
    funext k
    have h := congrFun (ProtocolRealization.edge_naturality a e) (ULift.up k)
    exact congrArg ULift.down h
  observation_naturality := fun v => by
    funext k
    exact congrFun (ProtocolRealization.observation_app a v) (ULift.up k)

/-- Extend a finite syntax morphism to every quotient execution.

This is the displayed `ext` of G-123(B0), definitionally the decoder map whose
all-path naturality was constructed above. -/
def displayedExt {P Q : ProtocolPresentation S O} (a : P ⟶ Q) :
    (decoder S O).obj P ⟶ (decoder S O).obj Q :=
  (decoder S O).map a

/-- Displayed restriction after extension recovers every finite vertex table.

This is one inverse equation required by G-123(B0). -/
@[simp]
theorem displayedRes_displayedExt {P Q : ProtocolPresentation S O} (a : P ⟶ Q) :
    displayedRes (displayedExt a) = a := by
  apply Hom.ext
  funext v x
  rfl

/-- Displayed extension after restriction recovers the complete morphism on all
objects and quotient executions.  This is the other G-123(B0) inverse. -/
@[simp]
theorem displayedExt_displayedRes {P Q : ProtocolPresentation S O}
    (a : (decoder S O).obj P ⟶ (decoder S O).obj Q) :
    displayedExt (displayedRes a) = a := by
  apply ProtocolRealization.Hom.ext
  ext q x
  cases x
  rfl

/-- The displayed B0 equivalence between complete maps and finite generator tables. -/
def displayedHomEquivGeneratorMap (P Q : ProtocolPresentation S O) :
    ((decoder S O).obj P ⟶ (decoder S O).obj Q) ≃ GeneratorMap P Q where
  toFun := displayedRes
  invFun := displayedExt
  left_inv := displayedExt_displayedRes
  right_inv := displayedRes_displayedExt

/-- Decoder evaluation is extension of syntax evaluation `J`.

This is the explicit protocol equation `F_Theta(f)=ext(J(f))` from G-123(B0). -/
theorem decoder_map_eq_displayedExt_evaluation {P Q : ProtocolPresentation S O}
    (a : P ⟶ Q) :
    (decoder S O).map a = displayedExt ((evaluationEquiv P Q) a) := rfl

/-- No-unfold recovery API for a decoded syntax map.

This combines the decoder equation with the displayed inverse law and is used
to prove G-123(B) faithfulness without exposing decoder internals. -/
@[simp]
theorem displayedRes_decoder_map {P Q : ProtocolPresentation S O} (a : P ⟶ Q) :
    displayedRes ((decoder S O).map a) = (evaluationEquiv P Q) a := by
  rw [decoder_map_eq_displayedExt_evaluation, displayedRes_displayedExt]

/-- Main G-123(B) faithfulness instance for the protocol decoder. -/
instance decoder_faithful : (decoder S O).Faithful where
  map_injective {P Q} a b h := by
    apply (evaluationEquiv P Q).injective
    have hres := congrArg displayedRes h
    simpa only [displayedRes_decoder_map] using hres

/-- Main G-123(B) fullness instance for the protocol decoder.

Every complete natural transformation over `O` is represented by its finite
vertex tables; no representability premise is imposed. -/
instance decoder_full : (decoder S O).Full where
  map_surjective {_ _} a :=
    ⟨displayedRes a, displayedExt_displayedRes a⟩

/-- A finite enumeration of the states at a named vertex.

This G-123(E) API uses only the finite-carrier premise of the independent
semantic object; the observation parameter `O(v)` remains unrestricted. -/
noncomputable def stateEquivFin (X : ProtocolRealization S O) (v : S.Vertex) :
    X.State v ≃ Fin (by letI := Fintype.ofFinite (X.State v); exact Fintype.card (X.State v)) := by
  letI := Fintype.ofFinite (X.State v)
  exact Fintype.equivFin (X.State v)

/-- The finite state count selected from an independent semantic object.

This is presentation-construction API for n1015 §3.1; it records cardinality,
not a completed execution map. -/
noncomputable def presentationCard (X : ProtocolRealization S O) (v : S.Vertex) : ℕ := by
  letI := Fintype.ofFinite (X.State v)
  exact Fintype.card (X.State v)

/-- Transport a named semantic operation through the finite state enumerations.

This constructs the edge table of the presentation selected for `X`; the
operation name and both typed endpoints are preserved. -/
noncomputable def presentationEdgeTable (X : ProtocolRealization S O)
    {v w : S.Vertex} (e : S.Edge v w) :
    Fin (presentationCard X v) → Fin (presentationCard X w) :=
  stateEquivFin X w ∘ X.edgeAction e ∘ (stateEquivFin X v).symm

/-- Computation rule for an enumerated named-operation table.

This no-unfold API exposes the conjugation used by G-123(E) while retaining
the original named edge and both endpoint enumerations. -/
@[simp]
theorem presentationEdgeTable_apply (X : ProtocolRealization S O)
    {v w : S.Vertex} (e : S.Edge v w) (k : Fin (presentationCard X v)) :
    presentationEdgeTable X e k =
      stateEquivFin X w (X.edgeAction e ((stateEquivFin X v).symm k)) := rfl

/-- Transport the semantic observation through the finite enumeration.

This constructs the state-observation field of the selected presentation and
does not require the observation codomain to be finite. -/
noncomputable def presentationObservationValue (X : ProtocolRealization S O)
    (v : S.Vertex) : Fin (presentationCard X v) → O.obj (S.vertexObject v) :=
  X.observe v ∘ (stateEquivFin X v).symm

/-- The finite path functor obtained by enumerating an independent realization.

This auxiliary API is generated only from the transported named-edge tables. -/
noncomputable def enumeratedPathFunctor (X : ProtocolRealization S O) :
    Paths S.Vertex ⥤ Type u :=
  S.pathFunctorOfEdgeAction (fun v => ULift.{u} (Fin (presentationCard X v)))
    (fun e k => ULift.up (presentationEdgeTable X e k.down))

/-- Evaluating the lifted enumerated path functor is exactly lifted finite-table
evaluation.  This API keeps the universe transport separate from execution. -/
@[simp]
theorem enumeratedPathFunctor_map_up (X : ProtocolRealization S O)
    {v w : S.Vertex} (p : Quiver.Path v w) (k : Fin (presentationCard X v)) :
    (enumeratedPathFunctor X).map p (ULift.up k) =
      ULift.up (S.evaluatePath (presentationEdgeTable X) p k) := by
  apply ULift.down_injective
  exact S.evaluatePath_ulift (presentationEdgeTable X) p (ULift.up k)

/-- Enumeration gives a natural isomorphism on every free execution path.

This path-inductive API proves that transporting only named-edge tables is
enough to recover every execution of the original semantic functor. -/
noncomputable def enumeratedPathIso (X : ProtocolRealization S O) :
    enumeratedPathFunctor X ≅
      CategoryTheory.Quotient.functor S.pathRelation ⋙ X.toFunctor :=
  Paths.liftNatIso
    (fun v => (Equiv.ulift.trans (stateEquivFin X v).symm).toIso) (fun e => by
    funext k
    exact (stateEquivFin X _).symm_apply_apply _)

/-- Component computation for the enumerated free-path isomorphism.

This no-unfold API states that its forward component lowers the finite index
and applies the inverse state enumeration. -/
@[simp]
theorem enumeratedPathIso_hom_app (X : ProtocolRealization S O) (v : S.Vertex)
    (k : ULift.{u} (Fin (presentationCard X v))) :
    (enumeratedPathIso X).hom.app v k = (stateEquivFin X v).symm k.down := rfl

/-- Pathwise computation furnished by the enumerated natural isomorphism.

This no-unfold API identifies transported finite-table execution with the
original semantic action for every finite path. -/
theorem enumeratedPathIso_naturality (X : ProtocolRealization S O)
    {v w : S.Vertex} (p : Quiver.Path v w) (k : Fin (presentationCard X v)) :
    (stateEquivFin X w).symm
        (S.evaluatePath (presentationEdgeTable X) p k) =
      X.pathAction p ((stateEquivFin X v).symm k) := by
  have h := congrFun ((enumeratedPathIso X).hom.naturality p) (ULift.up k)
  change (stateEquivFin X w).symm
      (((enumeratedPathFunctor X).map p (ULift.up k)).down) =
    X.pathAction p ((stateEquivFin X v).symm k) at h
  rw [enumeratedPathFunctor_map_up] at h
  exact h

/-- The transported edge tables satisfy every fixed generating path equation.

This discharges the presentation relation premise from quotient soundness and
the all-path naturality of `enumeratedPathIso`. -/
theorem presentation_relation_compatibility (X : ProtocolRealization S O)
    (r : S.RelationIndex) :
    S.evaluatePath (presentationEdgeTable X) (S.relationLeft r) =
      S.evaluatePath (presentationEdgeTable X) (S.relationRight r) := by
  funext k
  apply (stateEquivFin X (S.relationTarget r)).symm.injective
  calc
    (stateEquivFin X _).symm
        (S.evaluatePath (presentationEdgeTable X) (S.relationLeft r) k) =
        X.pathAction (S.relationLeft r) ((stateEquivFin X _).symm k) :=
      enumeratedPathIso_naturality X (S.relationLeft r) k
    _ = X.pathAction (S.relationRight r) ((stateEquivFin X _).symm k) := by
      exact congrFun (congrArg X.toFunctor.map (S.relation_sound r)) _
    _ = (stateEquivFin X _).symm
        (S.evaluatePath (presentationEdgeTable X) (S.relationRight r) k) :=
      (enumeratedPathIso_naturality X (S.relationRight r) k).symm

/-- The transported observations commute with every transported named edge.

This discharges the observation premise of the selected finite presentation
from the original natural transformation `X.observation`. -/
theorem presentation_observation_edge (X : ProtocolRealization S O)
    {v w : S.Vertex} (e : S.Edge v w) :
    presentationObservationValue X w ∘ presentationEdgeTable X e =
      O.map (S.edgeMorphism e) ∘ presentationObservationValue X v := by
  funext k
  change X.observe w
      ((stateEquivFin X w).symm
        (stateEquivFin X w (X.edgeAction e ((stateEquivFin X v).symm k)))) = _
  rw [(stateEquivFin X w).symm_apply_apply]
  exact congrFun (X.observation.naturality (S.edgeMorphism e))
    ((stateEquivFin X v).symm k)

/-- Select a finite presentation for every independent semantic protocol object.

All tables and well-formedness proofs are constructed from `X`, its finite
carriers, the fixed schema equations, and the fixed observation map. -/
noncomputable def presentationOf (X : ProtocolRealization S O) : ProtocolPresentation S O where
  card := presentationCard X
  edgeTable := presentationEdgeTable X
  relation_compatibility := presentation_relation_compatibility X
  observationValue := presentationObservationValue X
  observation_edge := presentation_observation_edge X

/-- Decoder edge-action computation for a finite protocol presentation.

This no-unfold API shows that the completed semantic functor executes a named
operation by the original finite table. -/
@[simp]
theorem decoderObject_edgeAction (P : ProtocolPresentation S O)
    {v w : S.Vertex} (e : S.Edge v w) (k : ULift.{u} (Fin (P.card v))) :
    ((decoder S O).obj P).edgeAction e k = ULift.up (P.edgeTable e k.down) := rfl

/-- Decoder observation computation for a finite protocol presentation.

This no-unfold API shows that universe transport does not change displayed
observation values. -/
@[simp]
theorem decoderObject_observe (P : ProtocolPresentation S O) (v : S.Vertex)
    (k : ULift.{u} (Fin (P.card v))) :
    ((decoder S O).obj P).observe v k = P.observationValue v k.down := rfl

/-- Generator map from the decoded selected presentation back to `X`.

Its components are the finite enumerations' inverse maps; edge and observation
compatibility are proved from the transported tables. -/
noncomputable def normalFormForwardGenerator (X : ProtocolRealization S O) :
    ProtocolRealization.GeneratorMap ((decoder S O).obj (presentationOf X)) X where
  component v := (Equiv.ulift.trans (stateEquivFin X v).symm)
  edge_naturality := fun {v w} e => by
    funext k
    exact (stateEquivFin X w).symm_apply_apply _
  observation_naturality := fun v => by
    funext k
    rfl

/-- Generator map from `X` into its decoded selected presentation.

Its components enumerate states and lift their indices; it is constructed from
the same enumerations as the forward generator map. -/
noncomputable def normalFormBackwardGenerator (X : ProtocolRealization S O) :
    ProtocolRealization.GeneratorMap X ((decoder S O).obj (presentationOf X)) where
  component v x := ULift.up (stateEquivFin X v x)
  edge_naturality := fun {v w} e => by
    funext x
    apply ULift.down_injective
    change stateEquivFin X w (X.edgeAction e x) =
      presentationEdgeTable X e (stateEquivFin X v x)
    rw [presentationEdgeTable_apply, Equiv.symm_apply_apply]
  observation_naturality := fun v => by
    funext x
    change presentationObservationValue X v (stateEquivFin X v x) = X.observe v x
    exact congrArg (X.observe v) ((stateEquivFin X v).symm_apply_apply x)

/-- Every semantic protocol object is isomorphic to the decoder of the finite
presentation constructed from its vertexwise enumerations.

The hom and inverse are extended from generator maps by the independently
proved path/quotient `ext`; both inverse equations hold on every state. -/
noncomputable def normalFormIso (X : ProtocolRealization S O) :
    (decoder S O).obj (presentationOf X) ≅ X where
  hom := ProtocolRealization.ext (normalFormForwardGenerator X)
  inv := ProtocolRealization.ext (normalFormBackwardGenerator X)
  hom_inv_id := by
    apply ProtocolRealization.Hom.ext
    ext q k
    change ULift.up
        (stateEquivFin X q.as ((stateEquivFin X q.as).symm k.down)) = k
    apply ULift.down_injective
    exact (stateEquivFin X q.as).apply_symm_apply k.down
  inv_hom_id := by
    apply ProtocolRealization.Hom.ext
    ext q x
    change (stateEquivFin X q.as).symm (stateEquivFin X q.as x) = x
    exact (stateEquivFin X q.as).symm_apply_apply x

/-- Vertex-component computation for the finite normal-form isomorphism.

This no-unfold API states that the forward map decodes the selected finite
state index through the enumeration of the original semantic carrier. -/
@[simp]
theorem normalFormIso_hom_app_vertex (X : ProtocolRealization S O)
    (v : S.Vertex) (k : ULift.{u} (Fin (presentationCard X v))) :
    ProtocolRealization.app (normalFormIso X).hom (S.vertexObject v) k =
      (stateEquivFin X v).symm k.down := rfl

/-- Vertex-component computation for the inverse finite normal-form map.

This no-unfold API states that the inverse enumerates an original semantic
state and lifts its finite index, without changing the represented state. -/
@[simp]
theorem normalFormIso_inv_app_vertex (X : ProtocolRealization S O)
    (v : S.Vertex) (x : X.State v) :
    ProtocolRealization.app (normalFormIso X).inv (S.vertexObject v) x =
      ULift.up (stateEquivFin X v x) := rfl

/-- Main G-123(B) retract-generation theorem for protocol realizations.

The retract is obtained from the constructed finite normal-form isomorphism;
no presentation or retract witness is an input. -/
theorem exists_decoder_retract (X : ProtocolRealization S O) :
    ∃ (P : ProtocolPresentation S O)
      (i : X ⟶ (decoder S O).obj P)
      (r : (decoder S O).obj P ⟶ X),
      i ≫ r = 𝟙 X := by
  exact ⟨presentationOf X, (normalFormIso X).inv, (normalFormIso X).hom,
    (normalFormIso X).inv_hom_id⟩

/-- Essential surjectivity of the protocol decoder is constructed from finite
state enumeration and the explicit `normalFormIso`. -/
noncomputable instance decoder_essSurj : (decoder S O).EssSurj :=
  Functor.EssSurj.mk fun X => ⟨presentationOf X, ⟨normalFormIso X⟩⟩

/-- The protocol decoder satisfies the Mathlib equivalence criterion using the
separately constructed fullness, faithfulness, and essential surjectivity. -/
noncomputable instance decoder_isEquivalence : (decoder S O).IsEquivalence where

/-- Finite protocol presentations reconstruct the independent semantic category.

This is the direct protocol equivalence required by G-123(E), n1015 §3.1; the
idempotent-completeness obligation remains a separate construction below. -/
noncomputable def presentationEquivalence :
    ProtocolPresentation S O ≌ ProtocolRealization S O :=
  (decoder S O).asEquivalence

end ProtocolPresentation

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
