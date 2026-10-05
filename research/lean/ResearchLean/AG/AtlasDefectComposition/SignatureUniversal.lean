import ResearchLean.AG.AtlasDefectComposition.SignatureGeometry
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Formal.Util.AssertStandardAxioms
/-! # 台署名の二つの普遍性

Implementation notes: decoderを持つ有限join商の射は商から署名へ向く。
通常の署名核の商の因子化は署名から評価先へ向く。両方で全射性とjoinを保持する。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AAT.AG.AtlasDefectComposition.SignatureGeometry
universe u v w
variable {T : Type u} {Ω : Type v} (S : T → Set Ω)
/-- Eの全セル復元を持つ有限join商。surjectionとdecoder squareは指定対象の条件。 -/
structure Presentation where
  /-- 有限join半束の台。 -/
  Carrier : Type v
  /-- 指定対象のjoin半束構造。 -/
  sup : SemilatticeSup Carrier
  /-- 指定対象のbottom。 -/
  bot : OrderBot Carrier
  /-- 指定対象の有限性。 -/
  finite : Finite Carrier
  /-- 元の全subsetからのbottom・joinを保つ商射。 -/
  encode : SupBotHom (Set T) Carrier
  /-- 全名付きセルを復元するbottom・join準同型。 -/
  decode : SupBotHom Carrier (Set Ω)
  /-- 指定対象では元のsubset全体からの全射性を要求する。 -/
  encode_surjective : Function.Surjective encode
  /-- decoderと商射の合成は実alpha。診断次元の一致では代替しない。 -/
  decode_encode : ∀ A, decode (encode A) = alpha S A
attribute [instance] Presentation.sup Presentation.bot Presentation.finite
/-- Eの指定圏の射。bottom・joinと両方の可換図式を保持する。 -/
structure PresentationHom (P Q : Presentation S) where
  /-- 指定join半束の準同型。 -/
  map : SupBotHom P.Carrier Q.Carrier
  /-- 元のsubsetからの商射と可換。 -/
  encode_comm : ∀ A, map (P.encode A) = Q.encode A
  /-- 元の全セルdecoderと可換。 -/
  decode_comm : ∀ x, Q.decode (map x) = P.decode x
/-- 指定射のAPI補題。計算写像の各元の一致で射全体が一致する。 -/
@[ext] theorem presentationHom_ext {P Q : Presentation S} {f g : PresentationHom S P Q}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  cases f
  cases g
  congr 1
  exact DFunLike.ext _ _ h
/-- 全セル復元図式を保持する指定射の恒等。 -/
def presentationHomId (P : Presentation S) : PresentationHom S P P where
  map := SupBotHom.id _
  encode_comm := fun _ => rfl
  decode_comm := fun _ => rfl
/-- 全セル復元図式を保持する指定射の合成。 -/
def presentationHomComp {P Q R : Presentation S}
    (f : PresentationHom S P Q) (g : PresentationHom S Q R) : PresentationHom S P R where
  map := g.map.comp f.map
  encode_comm := fun A => by rw [SupBotHom.comp_apply,f.encode_comm,g.encode_comm]
  decode_comm := fun x => by rw [SupBotHom.comp_apply,g.decode_comm,f.decode_comm]
/-- Eの有限join商と指定射を実圏としてまとめる。 -/
instance presentationCategory : Category (Presentation S) where
  Hom := PresentationHom S
  id := presentationHomId S
  comp := presentationHomComp S
  id_comp := fun _ => by ext x; rfl
  comp_id := fun _ => by ext x; rfl
  assoc := fun _ _ _ => by ext x; rfl
/-- 実署名の像と標準商射・包含decoderから作る指定対象。 -/
def signaturePresentation [Finite Ω] : Presentation S where
  Carrier := Signature S
  sup := inferInstance
  bot := inferInstance
  finite := inferInstance
  encode := sigmaHom S
  decode := inclusionHom S
  encode_surjective := sigma_surjective S
  decode_encode := fun _ => rfl
/-- Eの任意の復元可能商から署名へ向く指定射。全射性からdecoderの像を証明する。 -/
def terminalHom [Finite Ω] (P : Presentation S) : P ⟶ signaturePresentation S where
  map :=
    { toFun := fun x => ⟨P.decode x,by
        obtain ⟨A,rfl⟩ := P.encode_surjective x
        exact ⟨A,(P.decode_encode A).symm⟩⟩
      map_sup' := fun x y => Subtype.ext (map_sup P.decode x y)
      map_bot' := Subtype.ext (map_bot P.decode) }
  encode_comm := fun A => Subtype.ext (P.decode_encode A)
  decode_comm := fun _ => rfl
/-- 終射の公開評価則。元のdecoderを像へcorestrictしている。 -/
@[simp] theorem terminalHom_val [Finite Ω] (P : Presentation S) (x : P.Carrier) :
    ((terminalHom S P).map x).val = P.decode x := rfl
/-- Eの終射の一意性。全セルdecoder可換性を保持する射だけを量化する。 -/
theorem terminalHom_unique [Finite Ω] (P : Presentation S) (f : P ⟶ signaturePresentation S) :
    f = terminalHom S P := by
  apply presentationHom_ext
  intro x
  apply Subtype.ext
  exact f.decode_comm x
/-- Eの復元可能な有限join商の圏で、実署名が終対象となる。 -/
def signatureIsTerminal [Finite Ω] : IsTerminal (signaturePresentation S) :=
  IsTerminal.ofUniqueHom (terminalHom S) (terminalHom_unique S)
variable {L : Type w} [SemilatticeSup L] [OrderBot L]
variable (k : SupBotHom (Set T) L)
variable (hk : ∀ A B, alpha S A = alpha S B → k A = k B)
/-- 通常の商の逆向き因子化。実署名のcanonical閉集合代表でkを読む。 -/
def quotientFactor : SupBotHom (Signature S) L where
  toFun := fun X => k (gamma S X.val)
  map_sup' := by
    intro X Y
    change k (gamma S (X.val ∪ Y.val)) = k (gamma S X.val) ⊔ k (gamma S Y.val)
    rw [← map_sup k]
    apply hk
    change alpha S (gamma S (X ⊔ Y).val) = alpha S (gamma S X.val ∪ gamma S Y.val)
    rw [alpha_gamma_signature,alpha_union,alpha_gamma_signature,alpha_gamma_signature]
    rfl
  map_bot' := by
    change k (gamma S ∅) = ⊥
    rw [← map_bot k]
    apply hk
    change alpha S (gamma S (⊥ : Signature S).val) = alpha S ∅
    rw [alpha_gamma_signature,signature_bot_val,alpha_empty]
/-- 逆向き商因子化の公開元評価。指定kを同じ実署名上で復元する。 -/
@[simp] theorem quotientFactor_sigma (A : Set T) : quotientFactor S k hk (sigma S A) = k A :=
  hk _ _ (alpha_gamma_alpha S A)
/-- 通常の商因子化もbottom・join準同型として元の商射と可換である。 -/
theorem quotientFactor_comp : (quotientFactor S k hk).comp (sigmaHom S) = k := by
  ext A
  exact quotientFactor_sigma S k hk A
/-- 通常の商の因子化の一意性はsigmaの全射性から出る。 -/
theorem quotientFactor_unique (h : SupBotHom (Signature S) L)
    (hh : h.comp (sigmaHom S) = k) : h = quotientFactor S k hk := by
  ext X
  obtain ⟨A,rfl⟩ := sigma_surjective S X
  rw [quotientFactor_sigma]
  exact congrArg (fun f : SupBotHom (Set T) L => f A) hh
include hk in
/-- Eの通常の商の普遍性。終対象の射とは逆の向きの全一意因子化である。 -/
theorem quotient_universal : ∃! h : SupBotHom (Signature S) L, h.comp (sigmaHom S) = k :=
  ⟨quotientFactor S k hk,quotientFactor_comp S k hk,
    fun h hh => quotientFactor_unique S k hk h hh⟩
end AAT.AG.AtlasDefectComposition.SignatureGeometry
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SignatureGeometry
