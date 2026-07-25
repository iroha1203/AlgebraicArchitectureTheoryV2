import Formal.AG.SemanticRepair.Saga.EquationRealization

/-!
# Issue #3734: equation-system production route for the SAGA equation inputs

* `SupportAtomEquationSelection`: X.命題6.1A の selected 対応 `λ ↦ (i_λ, A_λ)`
  を、X.定義5.1 / III.定義11.3 の displayed Atom/equation coordinate 語彙
  (required index と architecture reading の Atom 単位選択)で受ける selected
  datum。本文が selected とするもの(対応そのもの)だけを field に持つ。
* `SupportAtomEquationSelection.realization`: `EquationSemanticRealization` の
  production constructor。命題6.1A の唯一の条件「restriction と可換する」を
  supplied field ではなく証明で放電する: support Atom を通じた factoring は
  `projection_natural` + `occRestrict_atom`(occurrence の台 Atom 保存)により
  restriction 可換性の十分条件である。命題6.1A の一般面は従来どおり
  `EquationSemanticRealization` が担い、本 constructor はそれを置き換えない
  (すべての realization がこの形で得られるとは主張しない)。
* `SupportAtomEquationSelection.displayedSource`: produced realization が読む
  displayed Atom/equation coordinate 族を III.定義11.3 の displayed equation
  source として束ねた生成物。defect は field ではなく生成される(#3733)。
* `realization_chiE_eq_interpret` と派生 vanishing 補題: produced `χ^E` の値は
  III.定理11.4 の generated interpretation(X.定義5.1 の `int_E`)と定義的に
  一致する。したがって #3732/#3733 の生成 chain(`witnessIdeal` →
  `obstructionIdeal` → quotient zero、fulfillment 経路)がそのまま適用され、
  再証明しない。
* `LiftFiberData.equationLiftSystem`: X.定義5.3 の幾何側入力規律
  「equation system は coefficient `Q_E` を生成し、base reading と local lifts
  は解こうとする局所 equation-lift problem を選ぶ」の Lean 実体。生成される
  のは `equationSitePresheaf`(生成 `Q_E`)上への C2 `liftSystem` engine の
  適用だけであり、lift-fiber datum(short exact sequence と base reading)は
  X.§1 入力6 のとおり selected のまま。
* `SagaEquationPacket.ofProduction`: 定理1.1 入力束を production route から
  組み立てる束ね constructor。旧 `Law.holds`、manual equation core、
  membership certificate、結論相当 field は入力に取らない。

Claim boundary: `P_E` 本体と local lift atlas、semantic 側入力(`P_sem` /
repair atlas)、state correspondence `β`、empty-overlap normalization は
X.§1 の selected/generated/proved 三分類のとおり selected のまま受け取る。
凍結 G-06 route(`LawEquationGeneratedPair` / `SagaComparison`)には依存しない。
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

universe u v x

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}
variable {𝒰 : MonomorphicOrderedCover S}

/-!
## X.命題6.1A: support-Atom factored selected 対応と realization の生成
-/

/--
X.命題6.1A の selected 対応 `λ ↦ (i_λ, A_λ)` を、X.定義5.1 / III.定義11.3 の
displayed Atom/equation coordinate `(A_a, i_a, a)` の形、すなわち support Atom
単位の選択として受ける selected datum。required 性は `RequiredIndex` subtype
で選択と同時に固定する(#3733 と同じ規約)。
-/
structure SupportAtomEquationSelection (S : Site.AATSite A) : Type (u + 1) where
  /-- 各 Atom に selected required equation index `i_a` を対応させる。 -/
  equationIndex : U.Atom -> S.equationSystem.RequiredIndex
  /-- 各 Atom に selected local architecture reading `A_a` を対応させる。 -/
  archReading : U.Atom -> ArchitectureObject U

namespace SupportAtomEquationSelection

variable (sel : SupportAtomEquationSelection S)
variable {P : SemanticRepairPresentation.{u, v} S R}

/--
X.命題6.1A の production constructor: support Atom を通じて factoring された
selected 対応から `EquationSemanticRealization` を生成する。命題6.1A の条件
「これらが restriction と可換する」は field として供給せず、
`projection_natural`(定義3.1 の occurrence projection の naturality)と
`occRestrict_atom`(restriction が台 Atom を保存すること)から証明する。
-/
def realization (P : SemanticRepairPresentation.{u, v} S R)
    (𝒰 : MonomorphicOrderedCover S) :
    EquationSemanticRealization P 𝒰 where
  lawIndex σ l :=
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
  lawIndex_required σ l :=
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).2
  lawIndex_natural {σ τ} f l := by
    show (sel.equationIndex (P.atomData.projection σ.ctx
        (P.atomData.restrictAtom f.hom l.1)).atom).1 =
      (sel.equationIndex (P.atomData.projection τ.ctx l.1).atom).1
    rw [P.atomData.projection_natural f.hom l.1, R.occRestrict_atom]
  archReading σ l :=
    sel.archReading (P.atomData.projection σ.ctx l.1).atom
  archReading_natural {σ τ} f l := by
    show sel.archReading (P.atomData.projection σ.ctx
        (P.atomData.restrictAtom f.hom l.1)).atom =
      sel.archReading (P.atomData.projection τ.ctx l.1).atom
    rw [P.atomData.projection_natural f.hom l.1, R.occRestrict_atom]

/-- Produced realization の selected equation index は Atom 単位選択の読み出し。 -/
@[simp] theorem realization_lawIndex (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).lawIndex σ l =
      (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1 :=
  rfl

/-- Produced realization の architecture reading は Atom 単位選択の読み出し。 -/
@[simp] theorem realization_archReading (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).archReading σ l =
      sel.archReading (P.atomData.projection σ.ctx l.1).atom :=
  rfl

/--
X.命題6.1A: produced `χ^E` の値式
`χ^E_V(λ) = [ε_{V,A_λ,i_λ,π_V(λ)}]`(#3732 の `equationResidual` +
`obstructionIdeal` からの生成、定義的一致)。
-/
theorem realization_chiE_apply (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l =
      Ideal.Quotient.mk (S.equationSystem.obstructionIdeal σ.ctx)
        (S.equationSystem.equationResidual σ.ctx
          (sel.archReading (P.atomData.projection σ.ctx l.1).atom)
          (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
          (P.atomData.projection σ.ctx l.1).atom) :=
  rfl

/-!
## III.定義11.3 / X.定義5.1: produced realization が読む displayed source
-/

/--
III.定義11.3: produced realization が読む displayed Atom/equation coordinate
族を displayed equation source として束ねた生成物。chart index は
intersection × Atom、defect は #3733 のとおり field ではなく生成される。
-/
def displayedSource (sel : SupportAtomEquationSelection S)
    (𝒰 : MonomorphicOrderedCover S) :
    LawAlgebra.DisplayedEquationSource S.equationSystem where
  Chart := IntersectionIndex 𝒰 × U.Atom
  chart q := q.1.ctx
  LocalInput _ := PUnit
  input _ := PUnit.unit
  objectOfLocalInput q _ := sel.archReading q.2
  equationIndex q := sel.equationIndex q.2
  supportAtom q := q.2

/--
X.定義5.1 / III.定理11.4: produced `χ^E` の値は displayed defect の generated
interpretation `int_E` と定義的に一致する。#3732 の interpretation 面が
そのまま新 route の値になる。
-/
theorem realization_chiE_eq_interpret (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l =
      LawAlgebra.LawEquationDefectSource.interpret (sel.displayedSource 𝒰)
        (σ, (P.atomData.projection σ.ctx l.1).atom) :=
  rfl

/--
III.定理11.4(#3732 の再利用): produced `χ^E` の値の零化は displayed defect の
generated obstruction ideal 所属と同値。
-/
theorem realization_chiE_eq_zero_iff_defect_mem_obstructionIdeal
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 ↔
      (sel.displayedSource 𝒰).defect
          (σ, (P.atomData.projection σ.ctx l.1).atom) PUnit.unit ∈
        S.equationSystem.obstructionIdeal σ.ctx := by
  rw [sel.realization_chiE_eq_interpret σ l]
  exact LawAlgebra.LawEquationDefectSource.interpret_eq_zero_iff_defect_mem_obstructionIdeal
    (sel.displayedSource 𝒰) (σ, (P.atomData.projection σ.ctx l.1).atom)

/--
III.定理11.4(#3732 の `witnessIdeal_le_obstructionIdeal` の再利用): selected
required equation の witness ideal に displayed defect が入れば produced `χ^E`
の値は零。
-/
theorem realization_chiE_eq_zero_of_defect_mem_witnessIdeal
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx)
    (hmem :
      (sel.displayedSource 𝒰).defect
          (σ, (P.atomData.projection σ.ctx l.1).atom) PUnit.unit ∈
        S.equationSystem.witnessIdeal σ.ctx
          (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 := by
  rw [sel.realization_chiE_eq_zero_iff_defect_mem_obstructionIdeal σ l]
  exact S.equationSystem.witnessIdeal_le_obstructionIdeal σ.ctx
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).2 hmem

/--
III.定理11.4(#3733 の fulfillment 経路の再利用): selected equation の
fulfillment は produced `χ^E` の値を零にする。
-/
theorem equationHolds_realization_chiE_eq_zero
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx)
    (hholds : S.equationSystem.EquationHolds
      (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
      (sel.archReading (P.atomData.projection σ.ctx l.1).atom)) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 := by
  rw [sel.realization_chiE_eq_interpret σ l]
  exact LawAlgebra.DisplayedEquationSource.equationHolds_defect_quotient_eq_zero
    (sel.displayedSource 𝒰) (σ, (P.atomData.projection σ.ctx l.1).atom)
    PUnit.unit hholds

end SupportAtomEquationSelection

/-!
## X.定義5.3: 生成 `Q_E` 上への幾何側入力規律
-/

namespace LiftFiberData

/--
X.定義5.3: 「equation system は coefficient `Q_E` を生成し、base reading と
local lifts は解こうとする局所 equation-lift problem を選ぶ」の Lean 実体。
selected lift-fiber datum(short exact sequence と base reading)を生成
`Q_E = equationSitePresheaf`(X.定義5.1、#3732 の `ObstructionQuotient` 再利用)
の上で C2 `liftSystem` engine に通した affine system。lift problem 自体は
X.§1 入力6 のとおり selected のまま。
-/
def equationLiftSystem {L B : SitePresheafData.{u, u} S}
    (D : LiftFiberData (equationSitePresheaf S) L B)
    (𝒰 : MonomorphicOrderedCover S) :
    AffineCoefficientLiftSystem.{u, u, u} (equationCoefficient S 𝒰) :=
  D.liftSystem 𝒰

/-- `equationLiftSystem` は C2 `liftSystem` engine の適用そのもの(再実装しない)。 -/
@[simp] theorem equationLiftSystem_eq_liftSystem
    {L B : SitePresheafData.{u, u} S}
    (D : LiftFiberData (equationSitePresheaf S) L B)
    (𝒰 : MonomorphicOrderedCover S) :
    D.equationLiftSystem 𝒰 = D.liftSystem 𝒰 :=
  rfl

end LiftFiberData

/-!
## R0 §4.9: 定理1.1 入力束の production 組み立て
-/

namespace SagaEquationPacket

/--
R0 §4.9: 定理1.1 入力束を production route から組み立てる。equation 側は
`SupportAtomEquationSelection`(入力3 の selected 対応)と selected lift-fiber
datum(入力6)から `realization` / `equationLiftSystem` で生成し、semantic 側
入力(入力1・5)、`β`(入力7)、normalization(入力8)は X.§1 の三分類の
とおり selected のまま受け取る。completeness 対(入力4)は従来どおり bundle に
入れず定理仮定として受ける。
-/
def ofProduction
    (R : AtomOccurrenceReading S) (𝒰 : MonomorphicOrderedCover S)
    (P : SemanticRepairPresentation.{u, v} S R)
    (sel : SupportAtomEquationSelection S)
    (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
    (repairAtlas : SemanticRepairAtlas Psem)
    {L B : SitePresheafData.{u, u} S}
    (fiber : LiftFiberData (equationSitePresheaf S) L B)
    (liftAtlas : CoefficientLiftAtlas (fiber.equationLiftSystem 𝒰))
    (stateCorrespondence :
      PrimaryStateCorrespondence (sel.realization P 𝒰).chiE Psem
        (fiber.equationLiftSystem 𝒰))
    (normalization :
      EmptyOverlapNormalization P 𝒰 Psem (fiber.equationLiftSystem 𝒰)) :
    SagaEquationPacket.{u, v, x, u} S where
  occurrenceReading := R
  cover := 𝒰
  presentation := P
  realization := sel.realization P 𝒰
  repairSystem := Psem
  repairAtlas := repairAtlas
  liftSystem := fiber.equationLiftSystem 𝒰
  liftAtlas := liftAtlas
  stateCorrespondence := stateCorrespondence
  normalization := normalization

variable (R : AtomOccurrenceReading S) (𝒰 : MonomorphicOrderedCover S)
  (P : SemanticRepairPresentation.{u, v} S R)
  (sel : SupportAtomEquationSelection S)
  (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
  (repairAtlas : SemanticRepairAtlas Psem)
  {L B : SitePresheafData.{u, u} S}
  (fiber : LiftFiberData (equationSitePresheaf S) L B)
  (liftAtlas : CoefficientLiftAtlas (fiber.equationLiftSystem 𝒰))
  (stateCorrespondence :
    PrimaryStateCorrespondence (sel.realization P 𝒰).chiE Psem
      (fiber.equationLiftSystem 𝒰))
  (normalization :
    EmptyOverlapNormalization P 𝒰 Psem (fiber.equationLiftSystem 𝒰))

/-- 組み立てた packet の realization は production constructor の生成物。 -/
@[simp] theorem ofProduction_realization :
    (ofProduction R 𝒰 P sel Psem repairAtlas fiber liftAtlas
        stateCorrespondence normalization).realization =
      sel.realization P 𝒰 :=
  rfl

/-- 組み立てた packet の lift system は生成 `Q_E` 上の典型例 instantiation。 -/
@[simp] theorem ofProduction_liftSystem :
    (ofProduction R 𝒰 P sel Psem repairAtlas fiber liftAtlas
        stateCorrespondence normalization).liftSystem =
      fiber.equationLiftSystem 𝒰 :=
  rfl

end SagaEquationPacket

end Saga
end SemanticRepair
end AAT.AG
