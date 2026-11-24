import Formal.SHIGURE.Part1.ContextSelectedCategories

/-! # Strict descent for ordinary models of selected theories

Objects and arrows of the matching category are ordinary local models and
ordinary model maps. The comparison with the graph construction preserves
their restriction along every declaration inclusion.
-/

universe u v

namespace SHIGURE
namespace DeclarationContext

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {I : Type v}

/-- A family of ordinary local models satisfying the equality on each overlap in (3.2). -/
structure OrdinaryMatch (piece : I → DeclarationContext P) where
  /-- The model of the actual selected theory of each piece. -/
  pieceModel (i : I) : Model (Selected.theory (piece i))
  /-- The restrictions are equal as ordinary models of the intersection theory. -/
  overlap_eq (i j : I) :
    (Selected.modelRestriction (overlapLeft piece i j)).obj (pieceModel i) =
    (Selected.modelRestriction (overlapRight piece i j)).obj (pieceModel j)

namespace OrdinaryMatch

variable {piece : I → DeclarationContext P}

/-- Local models determine the entire matching object. -/
@[ext] theorem ext {A B : OrdinaryMatch piece} (same : ∀ i, A.pieceModel i = B.pieceModel i) : A = B := by
  have pieces : A.pieceModel = B.pieceModel := funext same
  cases A
  cases B
  cases pieces
  rfl

/-- A matching ordinary arrow is a tuple of ordinary model maps agreeing on the overlaps. -/
structure Hom (A B : OrdinaryMatch piece) where
  /-- The underlying model arrow at each piece. -/
  pieceMap (i : I) : A.pieceModel i ⟶ B.pieceModel i
  /-- The restrictions agree after the two endpoint identifications. -/
  overlap_comm (i j : I) :
    (Selected.modelRestriction (overlapLeft piece i j)).map (pieceMap i) ≫ eqToHom (B.overlap_eq i j) =
      eqToHom (A.overlap_eq i j) ≫ (Selected.modelRestriction (overlapRight piece i j)).map (pieceMap j)

namespace Hom

variable {A B C : OrdinaryMatch piece}

/-- Equal components determine equal matching arrows. -/
@[ext] theorem ext {f g : Hom A B} (same : ∀ i, f.pieceMap i = g.pieceMap i) : f = g := by
  have pieces : f.pieceMap = g.pieceMap := funext same
  cases f
  cases g
  cases pieces
  rfl

/-- The matching identity consists of the local identities. -/
noncomputable def identity (A : OrdinaryMatch piece) : Hom A A where
  pieceMap i := 𝟙 (A.pieceModel i)
  overlap_comm i j := by
    rw [(Selected.modelRestriction (overlapLeft piece i j)).map_id,
      (Selected.modelRestriction (overlapRight piece i j)).map_id,
      Category.id_comp, Category.comp_id]

/-- Composition of matching model maps is componentwise. -/
noncomputable def comp (f : Hom A B) (g : Hom B C) : Hom A C where
  pieceMap i := f.pieceMap i ≫ g.pieceMap i
  overlap_comm i j := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, g.overlap_comm, ← Category.assoc,
      f.overlap_comm, Category.assoc]

end Hom

/-- Ordinary local models with their compatible model maps form a category. -/
noncomputable instance category : Category.{max u v} (OrdinaryMatch piece) where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp _ := Hom.ext (fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (fun _ => Category.assoc _ _ _)

/-- Projection to any piece is an ordinary model functor. -/
noncomputable def project (i : I) : OrdinaryMatch piece ⥤ Model (Selected.theory (piece i)) where
  obj A := A.pieceModel i
  map f := (show Hom _ _ from f).pieceMap i
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Move a matching square along equality of its four endpoints and heterogeneous equality of its arrows. -/
private theorem transportSquare {C : Type*} [Category C]
    {A B X Y A' B' X' Y' : C}
    {l : A ⟶ B} {r : X ⟶ Y} {l' : A' ⟶ B'} {r' : X' ⟶ Y'}
    {a : A = X} {b : B = Y} {a' : A' = X'} {b' : B' = Y'}
    (hA : A = A') (hB : B = B') (hX : X = X') (hY : Y = Y')
    (hl : l ≍ l') (hr : r ≍ r') (square : l ≫ eqToHom b = eqToHom a ≫ r) :
    l' ≫ eqToHom b' = eqToHom a' ≫ r' := by
  cases hA
  cases hB
  cases hX
  cases hY
  have left : l = l' := eq_of_heq hl
  have right : r = r' := eq_of_heq hr
  subst l'
  subst r'
  exact square

/-- Apply a functor to an overlap square, including the transports along object equalities. -/
private theorem mapSquare {C : Type*} {D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B X Y : C} {l : A ⟶ B} {r : X ⟶ Y}
    (a : A = X) (b : B = Y) (square : l ≫ eqToHom b = eqToHom a ≫ r) :
    F.map l ≫ eqToHom (congrArg F.obj b) = eqToHom (congrArg F.obj a) ≫ F.map r := by
  subst X
  subst Y
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at square ⊢
  rw [square]

/-- Equal functors have the same arrow action after the endpoints are identified. -/
private theorem mapHEq {C : Type*} {D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (same : F = G) {A B : C} (f : A ⟶ B) : F.map f ≍ G.map f := by
  subst G
  rfl

/-- Translate the graph model in each piece into its ordinary selected model. -/
noncomputable def readObj (A : Match piece) : OrdinaryMatch piece where
  pieceModel i := (Selected.readFunctor (piece i)).obj (A.pieceModel i)
  overlap_eq i j :=
    let L := Selected.read_res (overlapLeft piece i j)
    let R := Selected.read_res (overlapRight piece i j)
    (Functor.congr_obj L (A.pieceModel i)).symm.trans
      ((congrArg (Selected.readFunctor (inter (piece i) (piece j))).obj (A.overlap_eq i j)).trans
        (Functor.congr_obj R (A.pieceModel j)))

/-- Translate the ordinary model in each piece into its retained graph. -/
noncomputable def writeObj (A : OrdinaryMatch piece) : Match piece where
  pieceModel i := (Selected.writeFunctor (piece i)).obj (A.pieceModel i)
  overlap_eq i j :=
    let L := Selected.write_res (overlapLeft piece i j)
    let R := Selected.write_res (overlapRight piece i j)
    (Functor.congr_obj L (A.pieceModel i)).trans
      ((congrArg (Selected.writeFunctor (inter (piece i) (piece j))).obj (A.overlap_eq i j)).trans
        (Functor.congr_obj R (A.pieceModel j)).symm)

/-- The strict read on each piece sends graph matching maps to ordinary matching maps. -/
noncomputable def readFunctor : Match piece ⥤ OrdinaryMatch piece where
  obj := readObj
  map {A B} f := show Hom (readObj A) (readObj B) from {
    pieceMap i := (Selected.readFunctor (piece i)).map ((show Match.Hom A B from f).pieceMap i)
    overlap_comm i j := by
      let L := Selected.read_res (overlapLeft piece i j)
      let R := Selected.read_res (overlapRight piece i j)
      let f := (show Match.Hom A B from f)
      exact transportSquare (Functor.congr_obj L (A.pieceModel i)) (Functor.congr_obj L (B.pieceModel i))
        (Functor.congr_obj R (A.pieceModel j)) (Functor.congr_obj R (B.pieceModel j))
        (mapHEq L (f.pieceMap i)) (mapHEq R (f.pieceMap j))
        (mapSquare (Selected.readFunctor (inter (piece i) (piece j))) (A.overlap_eq i j)
          (B.overlap_eq i j) (f.overlap_comm i j)) }
  map_id A := Hom.ext fun i => (Selected.readFunctor (piece i)).map_id (A.pieceModel i)
  map_comp f g := Hom.ext fun i => (Selected.readFunctor (piece i)).map_comp
    ((show Match.Hom _ _ from f).pieceMap i) ((show Match.Hom _ _ from g).pieceMap i)

/-- The strict write on each piece sends ordinary matching maps to graph matching maps. -/
noncomputable def writeFunctor : OrdinaryMatch piece ⥤ Match piece where
  obj := writeObj
  map {A B} f := show Match.Hom (writeObj A) (writeObj B) from {
    pieceMap i := (Selected.writeFunctor (piece i)).map ((show Hom A B from f).pieceMap i)
    overlap_comm i j := by
      let L := (Selected.write_res (overlapLeft piece i j)).symm
      let R := (Selected.write_res (overlapRight piece i j)).symm
      let f := (show Hom A B from f)
      exact transportSquare (Functor.congr_obj L (A.pieceModel i)) (Functor.congr_obj L (B.pieceModel i))
        (Functor.congr_obj R (A.pieceModel j)) (Functor.congr_obj R (B.pieceModel j))
        (mapHEq L (f.pieceMap i)) (mapHEq R (f.pieceMap j))
        (mapSquare (Selected.writeFunctor (inter (piece i) (piece j))) (A.overlap_eq i j)
          (B.overlap_eq i j) (f.overlap_comm i j)) }
  map_id A := Match.Hom.ext fun i => (Selected.writeFunctor (piece i)).map_id (A.pieceModel i)
  map_comp f g := Match.Hom.ext fun i => (Selected.writeFunctor (piece i)).map_comp
    ((show Hom _ _ from f).pieceMap i) ((show Hom _ _ from g).pieceMap i)

/-- Reading and writing a family recovers the original graph family, including every arrow. -/
theorem read_comp_write : readFunctor (piece := piece) ⋙ writeFunctor = 𝟭 (Match piece) := by
  have objects (A : Match piece) : (readFunctor ⋙ writeFunctor).obj A = (𝟭 _).obj A :=
    Match.ext (fun i => Selected.write_read_model (A.pieceModel i))
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Match.Hom.ext
  intro i
  simp only [Functor.comp_map, readFunctor, writeFunctor, Match.comp_pieceMap, Match.eqToHom_pieceMap,
    Functor.id_map]
  exact Functor.congr_hom (Selected.read_comp_write (piece i)) ((show Match.Hom A B from f).pieceMap i)

/-- The component of a transport in the matching category is the transport of that component's endpoints. -/
private theorem eqToHom_pieceMap {A B : OrdinaryMatch piece} (same : A = B) (i : I) :
    (show Hom A B from eqToHom same).pieceMap i = eqToHom (congrArg (fun M => M.pieceModel i) same) := by
  subst B
  rfl

/-- Composition can be read as componentwise composition in each local model category. -/
@[simp] theorem comp_pieceMap {A B C : OrdinaryMatch piece} (f : A ⟶ B) (g : B ⟶ C) (i : I) :
    (show Hom A C from f ≫ g).pieceMap i =
      (show Hom A B from f).pieceMap i ≫ (show Hom B C from g).pieceMap i :=
  rfl

/-- Writing and reading a family recovers the original ordinary family, including every arrow. -/
theorem write_comp_read : writeFunctor (piece := piece) ⋙ readFunctor = 𝟭 (OrdinaryMatch piece) := by
  have objects (A : OrdinaryMatch piece) : (writeFunctor ⋙ readFunctor).obj A = (𝟭 _).obj A :=
    OrdinaryMatch.ext (fun i => Selected.read_write_model (A.pieceModel i))
  refine CategoryTheory.Functor.ext objects ?_
  intro A B f
  apply Hom.ext
  intro i
  simp only [Functor.comp_map, writeFunctor, readFunctor, comp_pieceMap, eqToHom_pieceMap,
    Functor.id_map]
  exact Functor.congr_hom (Selected.write_comp_read (piece i)) ((show Hom A B from f).pieceMap i)

/-- The ordinary and graph matching categories are strictly isomorphic. -/
noncomputable def categoryIso : Cat.of (Match piece) ≅ Cat.of (OrdinaryMatch piece) where
  hom := readFunctor.toCatHom
  inv := writeFunctor.toCatHom
  hom_inv_id := congrArg Functor.toCatHom read_comp_write
  inv_hom_id := congrArg Functor.toCatHom write_comp_read

end OrdinaryMatch
end DeclarationContext
end SHIGURE
