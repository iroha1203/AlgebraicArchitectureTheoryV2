import Formal.SHIGURE.Part2.Schemes.AffineDescentOverlaps

/-! # The projection diagram in coordinates -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

local notation "ℛ" => CommRingCat.of B
local notation "𝒮" => CommRingCat.of (B ⊗[A] B)
local notation "𝒯" => CommRingCat.of (B ⊗[A] (B ⊗[A] B))

/-- The ring homomorphism for a projection of the geometric double overlap. -/
abbrev affineDoubleRingHom (i : Fin 2) : ℛ ⟶ 𝒮 :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

/-- The ring homomorphism for a projection of the geometric triple overlap. -/
abbrev affineTripleRingHom (i : Fin 3) : ℛ ⟶ 𝒯 :=
  CommRingCat.ofHom (affineTripleEmbedding A B i).toRingHom

/-- The ring homomorphism for a pair projection of the geometric triple overlap. -/
abbrev affinePairRingHom (i j : Fin 3) : 𝒮 ⟶ 𝒯 :=
  CommRingCat.ofHom (affinePairEmbedding A B i j).toRingHom

/-- The left composite is the same coefficient map as the left triple projection. -/
theorem affinePairRingHom_comp_left (i j : Fin 3) :
    affineDoubleRingHom A B 0 ≫ affinePairRingHom A B i j = affineTripleRingHom A B i :=
  congrArg (fun f : B →ₐ[A] B ⊗[A] (B ⊗[A] B) => CommRingCat.ofHom (R := B) (S := B ⊗[A] (B ⊗[A] B)) f.toRingHom)
    (affinePairEmbedding_comp_left A B i j)

/-- The right composite is the same coefficient map as the right triple projection. -/
theorem affinePairRingHom_comp_right (i j : Fin 3) :
    affineDoubleRingHom A B 1 ≫ affinePairRingHom A B i j = affineTripleRingHom A B j :=
  congrArg (fun f : B →ₐ[A] B ⊗[A] (B ⊗[A] B) => CommRingCat.ofHom (R := B) (S := B ⊗[A] (B ⊗[A] B)) f.toRingHom)
    (affinePairEmbedding_comp_right A B i j)

end SHIGURE.SchemeDescent
