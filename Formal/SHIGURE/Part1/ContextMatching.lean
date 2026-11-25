import Formal.SHIGURE.Part1.ContextModels

/-! # Strict matching families and their category

Equality of the two reducts is the matching condition on every overlap.
For a matching arrow, the overlap equation transports its endpoints along
these equalities, and then compares the two restricted arrows.
-/

universe u v

namespace SHIGURE
namespace DeclarationContext

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {I : Type v}

/-- The intersection inclusions for a family of declaration contexts. -/
abbrev overlapLeft (piece : I → DeclarationContext P) (i j : I) : inter (piece i) (piece j) ≤ piece i :=
  inter_le_left (piece i) (piece j)

/-- The second inclusion of each pairwise intersection. -/
abbrev overlapRight (piece : I → DeclarationContext P) (i j : I) : inter (piece i) (piece j) ≤ piece j :=
  inter_le_right (piece i) (piece j)

/-- Equation (3.2): the reducts of two local models are literally equal on their common declarations. -/
structure Match (piece : I → DeclarationContext P) where
  /-- A model in each piece of the family. -/
  pieceModel (i : I) : Models (piece i)
  /-- The two restrictions on every overlap coincide. -/
  overlap_eq (i j : I) : (pieceModel i).restrict (overlapLeft piece i j) =
    (pieceModel j).restrict (overlapRight piece i j)

namespace Match

variable {piece : I → DeclarationContext P}

/-- Matching objects are determined by the individual local models. -/
@[ext] theorem ext {A B : Match piece} (same : ∀ i, A.pieceModel i = B.pieceModel i) : A = B := by
  have pieces : A.pieceModel = B.pieceModel := funext same
  cases A
  cases B
  cases pieces
  rfl

/-- A family of local structure-preserving arrows equal on each overlap after identifying endpoints. -/
structure Hom (A B : Match piece) where
  /-- A model map in each piece. -/
  pieceMap (i : I) : A.pieceModel i ⟶ B.pieceModel i
  /-- Transport along the object equalities makes the restricted maps equal. -/
  overlap_comm (i j : I) :
    (res (overlapLeft piece i j)).map (pieceMap i) ≫ eqToHom (B.overlap_eq i j) =
      eqToHom (A.overlap_eq i j) ≫ (res (overlapRight piece i j)).map (pieceMap j)

namespace Hom

variable {A B C : Match piece}

/-- Equal local maps give equal matching arrows. -/
@[ext] theorem ext {f g : Hom A B} (same : ∀ i, f.pieceMap i = g.pieceMap i) : f = g := by
  have pieces : f.pieceMap = g.pieceMap := funext same
  cases f
  cases g
  cases pieces
  rfl

/-- The component of the identity arrow at any piece is its identity. -/
noncomputable def identity (A : Match piece) : Hom A A where
  pieceMap i := 𝟙 (A.pieceModel i)
  overlap_comm i j := by simp only [Functor.map_id, res_obj, Category.id_comp, Category.comp_id]

/-- The overlap equation is preserved by componentwise composition. -/
noncomputable def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  pieceMap i := f.pieceMap i ≫ g.pieceMap i
  overlap_comm i j := by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.overlap_comm, ← Category.assoc, f.overlap_comm, Category.assoc]

end Hom

/-- Strict matching objects and their compatible local maps form a category. -/
noncomputable instance category : Category.{max u v} (Match piece) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp _ := Hom.ext (fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (fun _ => Category.assoc _ _ _)

/-- The identity matching arrow restricts to the individual identity. -/
@[simp] theorem id_pieceMap (A : Match piece) (i : I) :
    (show Hom A A from 𝟙 A).pieceMap i = 𝟙 (A.pieceModel i) :=
  rfl

/-- Matching arrows compose independently at each piece. -/
@[simp] theorem comp_pieceMap {A B C : Match piece} (f : A ⟶ B) (g : B ⟶ C) (i : I) :
    (show Hom A C from f ≫ g).pieceMap i =
      (show Hom A B from f).pieceMap i ≫ (show Hom B C from g).pieceMap i :=
  rfl

/-- Every piece projection is a functor. -/
noncomputable def project (i : I) : Match piece ⥤ Models (piece i) where
  obj A := A.pieceModel i
  map f := (show Hom _ _ from f).pieceMap i
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The projected model is the chosen member of the matching family. -/
theorem project_obj (i : I) (A : Match piece) : (project i).obj A = A.pieceModel i :=
  rfl

/-- The projected arrow is the chosen component, with the endpoint identifications. -/
theorem project_map (i : I) {A B : Match piece} (f : A ⟶ B) :
    (project i).map f ≍ (show Hom A B from f).pieceMap i :=
  HEq.rfl

/-- The underlying local arrow of an equality transport is the transported local equality. -/
theorem eqToHom_pieceMap {A B : Match piece} (same : A = B) (i : I) :
    (show Hom A B from eqToHom same).pieceMap i = eqToHom (congrArg (fun M => M.pieceModel i) same) := by
  subst B
  rfl

end Match
end DeclarationContext
end SHIGURE
