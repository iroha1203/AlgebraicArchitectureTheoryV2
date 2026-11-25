import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Positive predicates on a sheaf of assignments

Definition 4.1 interprets positive formulas by subsheaves and Laws by
inclusion. These operations work on any site and apply to the relative
Zariski site of the coefficient scheme.

## Implementation notes

A predicate is a mathlib subfunctor of the assignments whose sections glue.
Using a predicate on global sections would lose the local nature of a union
or a projection image. The sheafification of a subfunctor already expresses
that its defining sieve covers the test object.
-/

open CategoryTheory Opposite

universe u v w

namespace SHIGURE

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A predicate on a sheaf of assignments is a subfunctor whose sections glue. -/
structure SheafPredicate (F : Sheaf J (Type w)) where
  /-- Assignments satisfying the predicate at each test object. -/
  carrier : Subfunctor F.val
  /-- The satisfying assignments form a sheaf. -/
  isSheaf : Presieve.IsSheaf J carrier.toFunctor

namespace SheafPredicate

variable {F G : Sheaf J (Type w)}

/-- The restriction of the assignment sheaf to satisfying sections. -/
def toSheaf (P : SheafPredicate F) : Sheaf J (Type w) :=
  ⟨P.carrier.toFunctor, (isSheaf_iff_isSheaf_of_type J _).mpr P.isSheaf⟩

/-- Include the satisfying assignments into all assignments. -/
def inclusion (P : SheafPredicate F) : P.toSheaf ⟶ F :=
  ⟨P.carrier.ι⟩

/-- A presheaf of satisfying assignments determines a subsheaf by local membership. -/
def ofLocal (P : Subfunctor F.val) : SheafPredicate F :=
  ⟨P.sheafify J, P.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J F.val).mp F.cond)⟩

/-- Locally satisfying the predicate means its sieve of satisfying restrictions covers. -/
theorem mem_ofLocal_iff (P : Subfunctor F.val) (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (ofLocal (F := F) P).carrier.obj U ↔ P.sieveOfSection x ∈ J U.unop :=
  Iff.rfl

/-- A pair of terms with the same target interprets equality by the equalizer predicate. -/
def equal (f g : F ⟶ G) : SheafPredicate F where
  carrier :=
    { obj := fun U => {x | f.val.app U x = g.val.app U x}
      map := by
        intro U V i x hx
        change f.val.app V (F.val.map i x) = g.val.app V (F.val.map i x)
        rw [FunctorToTypes.naturality F.val G.val f.val, FunctorToTypes.naturality F.val G.val g.val]
        exact congrArg (G.val.map i) hx }
  isSheaf := by
    apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J F.val).mp F.cond)).mpr
    intro U x hx
    change f.val.app U x = g.val.app U x
    have hs := (isSheaf_iff_isSheaf_of_type J G.val).mp G.cond
    apply (hs _ hx).isSeparatedFor.ext
    intro V i hi
    rw [← FunctorToTypes.naturality F.val G.val f.val, ← FunctorToTypes.naturality F.val G.val g.val]
    exact hi

/-- An assignment satisfies the equality atom exactly when the two sections agree. -/
@[simp]
theorem mem_equal_iff (f g : F ⟶ G) (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (equal f g).carrier.obj U ↔ f.val.app U x = g.val.app U x :=
  Iff.rfl

/-- A relation, domain or operation graph is pulled back along its tuple of variables. -/
def preimage (P : SheafPredicate G) (f : F ⟶ G) : SheafPredicate F where
  carrier := P.carrier.preimage f.val
  isSheaf := by
    apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J F.val).mp F.cond)).mpr
    intro U x hx
    change f.val.app U x ∈ P.carrier.obj U
    apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J G.val).mp G.cond)).mp P.isSheaf
    exact J.superset_covering (by
      intro V i hi
      change G.val.map i.op (f.val.app U x) ∈ P.carrier.obj (op V)
      rw [← FunctorToTypes.naturality F.val G.val f.val]
      exact hi) hx

/-- A map preserving membership of a subsheaf restricts to a map of the satisfying sections. -/
def mapAlong (f : F ⟶ G) {P : SheafPredicate F} {Q : SheafPredicate G}
    (h : P.carrier ≤ (Q.preimage f).carrier) : P.toSheaf ⟶ Q.toSheaf :=
  ⟨Subfunctor.lift (P.carrier.ι ≫ f.val) <| by
    rintro U _ ⟨x, rfl⟩
    exact h U x.property⟩

/-- The identity preserves membership of every predicate. -/
theorem respects_id (P : SheafPredicate F) : P.carrier ≤ (P.preimage (𝟙 F)).carrier :=
  le_rfl

/-- Preserving membership in two steps preserves membership under the composite. -/
theorem respects_comp {D : Sheaf J (Type w)} {P : SheafPredicate F} {Q : SheafPredicate G}
    {N : SheafPredicate D} {f : F ⟶ G} {g : G ⟶ D}
    (hf : P.carrier ≤ (Q.preimage f).carrier) (hg : Q.carrier ≤ (N.preimage g).carrier) :
    P.carrier ≤ (N.preimage (f ≫ g)).carrier :=
  fun U _ hx => hg U (hf U hx)

/-- Restricting the identity to the satisfying sections gives their identity. -/
@[simp]
theorem mapAlong_id (P : SheafPredicate F) :
    mapAlong (𝟙 F) (respects_id P) = 𝟙 P.toSheaf := by
  apply Sheaf.Hom.ext
  ext U x
  exact Subtype.ext rfl

/-- The maps on satisfying sections compose with the same order as the original maps. -/
theorem mapAlong_comp {D : Sheaf J (Type w)} {P : SheafPredicate F} {Q : SheafPredicate G}
    {N : SheafPredicate D} {f : F ⟶ G} {g : G ⟶ D}
    (hf : P.carrier ≤ (Q.preimage f).carrier) (hg : Q.carrier ≤ (N.preimage g).carrier) :
    mapAlong (f ≫ g) (respects_comp hf hg) = mapAlong f hf ≫ mapAlong g hg := by
  apply Sheaf.Hom.ext
  ext U x
  exact Subtype.ext rfl

/-- Truth is satisfied by every assignment. -/
def truth : SheafPredicate F :=
  ofLocal ⊤

/-- Falsehood is the least subsheaf. Its section on an empty test is supplied by the empty cover. -/
def falsehood : SheafPredicate F :=
  ofLocal ⊥

/-- Conjunction is intersection of the two subsheaves of assignments. -/
def conj (P Q : SheafPredicate F) : SheafPredicate F where
  carrier := P.carrier ⊓ Q.carrier
  isSheaf := by
    have hs := (isSheaf_iff_isSheaf_of_type J F.val).mp F.cond
    apply (Subfunctor.isSheaf_iff _ hs).mpr
    intro U x hx
    change x ∈ P.carrier.obj U ∧ x ∈ Q.carrier.obj U
    have left : P.carrier.sieveOfSection x ∈ J U.unop := by
      refine J.superset_covering ?_ hx
      intro _ _ hi
      exact hi.1
    have right : Q.carrier.sieveOfSection x ∈ J U.unop := by
      refine J.superset_covering ?_ hx
      intro _ _ hi
      exact hi.2
    exact ⟨(Subfunctor.isSheaf_iff _ hs).mp P.isSheaf U x left,
      (Subfunctor.isSheaf_iff _ hs).mp Q.isSheaf U x right⟩

/-- To satisfy a conjunction, the same section must satisfy both predicates. -/
@[simp]
theorem mem_conj_iff (P Q : SheafPredicate F) (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (conj P Q).carrier.obj U ↔ x ∈ P.carrier.obj U ∧ x ∈ Q.carrier.obj U :=
  Iff.rfl

/-- Disjunction is the subsheaf union, obtained by gluing the objectwise union. -/
def disj (P Q : SheafPredicate F) : SheafPredicate F :=
  ofLocal (P.carrier ⊔ Q.carrier)

/-- A disjunction holds where the sieve on which one of the disjuncts holds covers the test object. -/
theorem mem_disj_iff (P Q : SheafPredicate F) (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (disj P Q).carrier.obj U ↔ (P.carrier ⊔ Q.carrier).sieveOfSection x ∈ J U.unop :=
  Iff.rfl

/-- Existential quantification takes the image subsheaf under the projection of assignments. -/
def existsAlong (p : G ⟶ F) (Q : SheafPredicate G) : SheafPredicate F :=
  ofLocal (Subfunctor.range (Q.carrier.ι ≫ p.val))

/-- Existential membership holds on a covering sieve of restrictions having a witness. -/
theorem mem_existsAlong_iff (p : G ⟶ F) (Q : SheafPredicate G) (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (existsAlong p Q).carrier.obj U ↔
      (Subfunctor.range (Q.carrier.ι ≫ p.val)).sieveOfSection x ∈ J U.unop :=
  Iff.rfl

/-- The image along a subsheaf inclusion consists of precisely the sections whose
domain witness satisfies the predicate. This computes the graphs of partial operations. -/
theorem mem_existsAlong_inclusion_iff (P : SheafPredicate F) (Q : SheafPredicate P.toSheaf)
    (U : Cᵒᵖ) (x : F.val.obj U) :
    x ∈ (existsAlong P.inclusion Q).carrier.obj U ↔
      ∃ h : x ∈ P.carrier.obj U, (⟨x, h⟩ : P.toSheaf.val.obj U) ∈ Q.carrier.obj U := by
  constructor
  · intro h
    have cover := (mem_existsAlong_iff P.inclusion Q U x).mp h
    have hp : x ∈ P.carrier.obj U := by
      apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J _).mp F.cond)).mp P.isSheaf
      refine J.superset_covering ?_ cover
      rintro V f ⟨y, hy⟩
      change y.val.val = F.val.map f.op x at hy
      change F.val.map f.op x ∈ P.carrier.obj (op V)
      exact hy ▸ y.val.property
    refine ⟨hp, ?_⟩
    apply (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type J _).mp P.toSheaf.cond)).mp Q.isSheaf
    refine J.superset_covering ?_ cover
    rintro V f ⟨y, hy⟩
    have hy' : y.val = P.toSheaf.val.map f.op ⟨x, hp⟩ := Subtype.ext hy
    change P.toSheaf.val.map f.op ⟨x, hp⟩ ∈ Q.carrier.obj (op V)
    exact hy' ▸ y.property
  · rintro ⟨hp, hq⟩
    exact (Subfunctor.le_sheafify J _) U ⟨⟨⟨x, hp⟩, hq⟩, rfl⟩

/-- A Law holds when its antecedent subsheaf is contained in its consequent subsheaf. -/
def holds (input output : SheafPredicate F) : Prop :=
  input.carrier ≤ output.carrier

end SheafPredicate

end SHIGURE
