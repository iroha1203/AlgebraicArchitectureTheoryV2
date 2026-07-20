import Formal.AG.RepresentationAnalysis.AATSch
import Mathlib.CategoryTheory.Category.Cat

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

open CategoryTheory

universe u v w x z

/-- VII.定義3.1: indexed family of analytic representations. -/
structure RepresentationFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  Index : Type z
  Target : Index → CategoryTheory.Cat.{z, z}
  representation : ∀ i : Index, AnalyticRepresentation p (Target i)

namespace RepresentationFamily

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}

/-- VII.定義5.1 precursor: read an object through the selected representation. -/
def Read (F : RepresentationFamily p) (i : F.Index) (X : AATSch p) : F.Target i :=
  (F.representation i).obj X

/-- VII.定義3.1: the representation stored at an index. -/
def Rep (F : RepresentationFamily p) (i : F.Index) :
    AnalyticRepresentation p (F.Target i) :=
  F.representation i

/-- VII.定義3.1: reading accessor is the representation object map. -/
theorem read_eq_obj (F : RepresentationFamily p) (i : F.Index) (X : AATSch p) :
    F.Read i X = (F.Rep i).obj X :=
  rfl

end RepresentationFamily

/--
VII.定義4.1-4.3: selected structural and analytic notions used by a
representation family.

These predicates are deliberately relative to the chosen family.  They do not
assert that every structural notion is detected by every representation.
-/
structure RepresentationNotions {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
    (F : RepresentationFamily p) where
  structuralZero : AATSch p -> Prop
  structuralObstruction : AATSch p -> Prop
  selectedIso : AATSch p -> AATSch p -> Prop
  selectedMorphismEq :
    ∀ {X Y : AATSch p}, (X ⟶ Y) -> (X ⟶ Y) -> Prop
  analyticZero : ∀ i : F.Index, F.Target i -> Prop
  analyticObstruction : ∀ i : F.Index, F.Target i -> Prop
  analyticIso : ∀ i : F.Index, F.Target i -> F.Target i -> Prop
  analyticMorphismEq :
    ∀ i : F.Index, {X Y : AATSch p} ->
      (f g : X ⟶ Y) ->
        ((F.Rep i).obj X ⟶ (F.Rep i).obj Y) ->
        ((F.Rep i).obj X ⟶ (F.Rep i).obj Y) -> Prop

/--
VII.定義4.2: assumption package required for reflection claims.

Reflection is never built into a representation by default; coverage, witness
completeness, axis exactness, and coefficient discipline remain explicit.
-/
structure ReflectionAssumptions where
  coverage : Prop
  witnessCompleteness : Prop
  axisExactness : Prop
  coefficientDiscipline : Prop

namespace ReflectionAssumptions

/-- VII.定義4.2: all reflection assumptions are available. -/
def Holds (A : ReflectionAssumptions) : Prop :=
  A.coverage ∧ A.witnessCompleteness ∧ A.axisExactness ∧ A.coefficientDiscipline

/-- VII.定義4.2: expose coverage from a satisfied assumption package. -/
theorem coverage_holds {A : ReflectionAssumptions} (h : A.Holds) :
    A.coverage :=
  h.1

/-- VII.定義4.2: expose witness completeness from a satisfied assumption package. -/
theorem witnessCompleteness_holds {A : ReflectionAssumptions} (h : A.Holds) :
    A.witnessCompleteness :=
  h.2.1

/-- VII.定義4.2: expose axis exactness from a satisfied assumption package. -/
theorem axisExactness_holds {A : ReflectionAssumptions} (h : A.Holds) :
    A.axisExactness :=
  h.2.2.1

/-- VII.定義4.2: expose coefficient discipline from a satisfied assumption package. -/
theorem coefficientDiscipline_holds {A : ReflectionAssumptions} (h : A.Holds) :
    A.coefficientDiscipline :=
  h.2.2.2

end ReflectionAssumptions

namespace RepresentationNotions

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}
variable {F : RepresentationFamily p}

/-- VII.定義4.1: structural zero is preserved by every selected reading. -/
def ZeroPreserving (N : RepresentationNotions F) : Prop :=
  ∀ (i : F.Index) (X : AATSch p),
    N.structuralZero X -> N.analyticZero i (F.Read i X)

/-- VII.定義4.2: analytic zero reflects structural zero under assumptions. -/
def ZeroReflecting (N : RepresentationNotions F) (A : ReflectionAssumptions) : Prop :=
  A.Holds ->
    ∀ X : AATSch p, (∀ i : F.Index, N.analyticZero i (F.Read i X)) ->
      N.structuralZero X

/-- VII.定義4.1: selected obstruction readings are preserved. -/
def ObstructionPreserving (N : RepresentationNotions F) : Prop :=
  ∀ (i : F.Index) (X : AATSch p),
    N.structuralObstruction X -> N.analyticObstruction i (F.Read i X)

/-- VII.定義4.2: analytic obstruction readings reflect structural obstruction. -/
def ObstructionReflecting (N : RepresentationNotions F) (A : ReflectionAssumptions) : Prop :=
  A.Holds ->
    ∀ X : AATSch p, (∀ i : F.Index, N.analyticObstruction i (F.Read i X)) ->
      N.structuralObstruction X

/-- VII.定義4.1: selected isomorphism is preserved by every reading. -/
def IsoPreserving (N : RepresentationNotions F) : Prop :=
  ∀ (i : F.Index) (X Y : AATSch p),
    N.selectedIso X Y -> N.analyticIso i (F.Read i X) (F.Read i Y)

/-- VII.定義4.2: analytic isomorphism reflects selected structural isomorphism. -/
def IsoReflecting (N : RepresentationNotions F) (A : ReflectionAssumptions) : Prop :=
  A.Holds ->
    ∀ X Y : AATSch p,
      (∀ i : F.Index, N.analyticIso i (F.Read i X) (F.Read i Y)) ->
        N.selectedIso X Y

/-- VII.定義4.1: selected morphism equality is preserved by every reading. -/
def MorphismEqPreserving (N : RepresentationNotions F) : Prop :=
  ∀ (i : F.Index) {X Y : AATSch p} (f g : X ⟶ Y),
    N.selectedMorphismEq f g -> N.analyticMorphismEq i f g ((F.Rep i).map f) ((F.Rep i).map g)

/-- VII.定義4.2: analytic morphism equality reflects selected morphism equality. -/
def MorphismEqReflecting (N : RepresentationNotions F) (A : ReflectionAssumptions) :
  Prop :=
  A.Holds ->
    ∀ {X Y : AATSch p} (f g : X ⟶ Y),
      (∀ i : F.Index, N.analyticMorphismEq i f g ((F.Rep i).map f) ((F.Rep i).map g)) ->
        N.selectedMorphismEq f g

/-- VII.定義4.3: conservative for selected zero, obstruction, and iso notions. -/
def Conservative (N : RepresentationNotions F) (A : ReflectionAssumptions) : Prop :=
  N.ZeroReflecting A ∧ N.ObstructionReflecting A ∧ N.IsoReflecting A

/-- VII.定義4.3: faithful for selected morphism equality. -/
def Faithful (N : RepresentationNotions F) (A : ReflectionAssumptions) : Prop :=
  N.MorphismEqReflecting A

variable {N : RepresentationNotions F}
variable {A : ReflectionAssumptions}

/-- VII.定義4.1: apply zero preservation. -/
theorem analyticZero_of_structuralZero (h : N.ZeroPreserving)
    (i : F.Index) {X : AATSch p} (hzero : N.structuralZero X) :
    N.analyticZero i (F.Read i X) :=
  h i X hzero

/-- VII.定義4.2: apply zero reflection under explicit assumptions. -/
theorem structuralZero_of_analyticZero (h : N.ZeroReflecting A)
    (hA : A.Holds) {X : AATSch p}
    (hzero : ∀ i : F.Index, N.analyticZero i (F.Read i X)) :
    N.structuralZero X :=
  h hA X hzero

/-- VII.定義4.1: apply obstruction preservation. -/
theorem analyticObstruction_of_structuralObstruction (h : N.ObstructionPreserving)
    (i : F.Index) {X : AATSch p} (hobs : N.structuralObstruction X) :
    N.analyticObstruction i (F.Read i X) :=
  h i X hobs

/-- VII.定義4.2: apply obstruction reflection under explicit assumptions. -/
theorem structuralObstruction_of_analyticObstruction (h : N.ObstructionReflecting A)
    (hA : A.Holds) {X : AATSch p}
    (hobs : ∀ i : F.Index, N.analyticObstruction i (F.Read i X)) :
    N.structuralObstruction X :=
  h hA X hobs

/-- VII.定義4.1: apply selected isomorphism preservation. -/
theorem analyticIso_of_selectedIso (h : N.IsoPreserving)
    (i : F.Index) {X Y : AATSch p} (hiso : N.selectedIso X Y) :
    N.analyticIso i (F.Read i X) (F.Read i Y) :=
  h i X Y hiso

/-- VII.定義4.2: apply selected isomorphism reflection. -/
theorem selectedIso_of_analyticIso (h : N.IsoReflecting A)
    (hA : A.Holds) {X Y : AATSch p}
    (hiso : ∀ i : F.Index, N.analyticIso i (F.Read i X) (F.Read i Y)) :
    N.selectedIso X Y :=
  h hA X Y hiso

/-- VII.定義4.1: apply selected morphism equality preservation. -/
theorem analyticMorphismEq_of_selectedMorphismEq (h : N.MorphismEqPreserving)
    (i : F.Index) {X Y : AATSch p} {f g : X ⟶ Y}
    (heq : N.selectedMorphismEq f g) :
    N.analyticMorphismEq i f g ((F.Rep i).map f) ((F.Rep i).map g) :=
  h i f g heq

/-- VII.定義4.2: apply selected morphism equality reflection. -/
theorem selectedMorphismEq_of_analyticMorphismEq (h : N.MorphismEqReflecting A)
    (hA : A.Holds) {X Y : AATSch p} {f g : X ⟶ Y}
    (heq : ∀ i : F.Index,
      N.analyticMorphismEq i f g ((F.Rep i).map f) ((F.Rep i).map g)) :
    N.selectedMorphismEq f g :=
  h hA f g heq

/-- VII.定義4.3: conservative families reflect selected zero. -/
theorem structuralZero_of_conservative (h : N.Conservative A)
    (hA : A.Holds) {X : AATSch p}
    (hzero : ∀ i : F.Index, N.analyticZero i (F.Read i X)) :
    N.structuralZero X :=
  N.structuralZero_of_analyticZero h.1 hA hzero

/-- VII.定義4.3: faithful families reflect selected morphism equality. -/
theorem selectedMorphismEq_of_faithful (h : N.Faithful A)
    (hA : A.Holds) {X Y : AATSch p} {f g : X ⟶ Y}
    (heq : ∀ i : F.Index,
      N.analyticMorphismEq i f g ((F.Rep i).map f) ((F.Rep i).map g)) :
    N.selectedMorphismEq f g :=
  N.selectedMorphismEq_of_analyticMorphismEq h hA heq

end RepresentationNotions

end RepresentationAnalysis
end AAT.AG
