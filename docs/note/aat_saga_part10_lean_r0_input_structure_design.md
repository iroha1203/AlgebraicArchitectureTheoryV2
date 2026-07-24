# SAGA 中心定理 Lean 形式化 R0: 入力 structure 設計(Issue #3757)

status: R0 fixed(本 note が #3757 R0 の固定成果物)
tracking: #3757(親)、C1 #3762 以降の各子 Issue
source of truth: `docs/aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md`(現行 main)

本 note は Issue #3757 の R0 三項目を固定する。

1. 定理1.1(SAGA 中心定理)の8つの番号付き入力と monomorphic AAT cover の
   Lean structure 設計(§3–§5)
2. 旧 `Formal/AG/SemanticRepair/*` の宣言単位の存廃仮決め(§6。最終処分は C8 #3769)
3. G-07 対応表の R0 固定 map としての採用(§7)

参照規約は #3757 本文の照合規則(番号+名前の対)に従う。本 note の定理・定義番号は
すべて現行 main の Part X 本文と突合済みである。

## 問い

定理1.1 の8入力と monomorphic AAT cover を、どの Lean structure 群へ固定すれば、
C1–C8 が本文 §9 依存図と同型の import / proof 依存で構成でき、かつ
縮小禁止リスト(同値・逆写像・微分可換性・cocycle 性・`H¹` 同値の certificate field 化禁止)を
構造的に満たせるか。

## 1. 基底設定と既存資産の接続点

新 route は次の既存 declaration を接続点として使う。いずれも実在を確認済み。

| 接続点 | 場所 | 役割 |
| --- | --- | --- |
| `Site.AATSite` | `Formal/AG/Site/Geometry.lean:18` | site 全体(contextPreorder / equationSystem / overlap を束ねる)。新 structure 群の基底 |
| `Site.ContextOverlapPullback` | `Formal/AG/Site/ContextCategory.lean:529` | II.仮定4.3 の overlap package。cover の `U_ij` 生成の canonical 供給源 |
| `Cohomology.CoverRelativeCechCover` / `CoverRelativeCechComplex` | `Formal/AG/Cohomology/CechComplex.lean` | 第IV部の全 ordered tuple 複体。補題2.1A の bridge 先(`AdditiveCechH1` 面) |
| `ArchitecturalEquationSystem` | `Formal/AG/Equation/Basic.lean:42` | equation system `E`(Part I 定義7.1–7.3) |
| `ArchitecturalEquationSystem.ObstructionQuotient` / `obstructionQuotientRestrict` | `Formal/AG/LawAlgebra/LawEquation.lean:108,114` | `Q_E(V) = O_E(V)/I_Ob^E(V)` と restriction(Part III 定理11.4 の Lean 実体)。C3a の realization target |
| `Site.FinitePoset` 系(第II部 命題4.2 model) | `Formal/AG/Site/FinitePoset.lean` ほか | mono 自動成立 instance の供給源(C1) |

site category `S.category = ContextCategoryObject` は thin category である。したがって
図式可換条件は自動で成立し、新 structure 群は morphism データと lift データだけを持てばよい。

## 2. 配置と namespace

新 route は既存 G-06 route(§6)と衝突しない新 subtree に置く。

```text
namespace: AAT.AG.SemanticRepair.Saga

Formal/AG/SemanticRepair/Saga/Cover.lean            -- C1: mono cover + 増加添字複体 + 補題2.1A
Formal/AG/SemanticRepair/Saga/Presentation.lean     -- C1: 定義3.1–3.4(M_sem)
Formal/AG/SemanticRepair/Saga/RepairTorsor.lean     -- C2: 定義4.1–系4.5
Formal/AG/SemanticRepair/Saga/EquationLift.lean     -- C2: 定義5.3–補題5.4
Formal/AG/SemanticRepair/Saga/Exactness.lean        -- C3: 定義6.1–例6.6(Φ)
Formal/AG/SemanticRepair/Saga/EquationRealization.lean -- C3a: 命題6.1A・系6.7
Formal/AG/SemanticRepair/Saga/CochainComparison.lean   -- C4: 定義7.1–定理7.6(κ, H¹)
Formal/AG/SemanticRepair/Saga/TrueSheafDescent.lean    -- C5: 定義8.1–系8.3
Formal/AG/SemanticRepair/Saga/CircleWitness.lean       -- C7: 例10.2 / 付録B.9
```

ファイル分割は実装時に多少調整してよいが、§9 依存図と同型の import 依存
(C1 ← C2 ← C3 ← C3a ← C4 ← C5、C7 は C4 後)を壊す統合はしない。

## 3. Monomorphic AAT cover の structure 設計(定理1.1 前提)

```lean
/-- X.§1: 全順序添字つき monomorphic AAT cover。
overlap は selected data として持ち、pullback 性は lift field で持つ
(thin category なので可換条件と一意性は自動)。 -/
structure MonomorphicOrderedCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  base : S.category                                    -- W
  Index : Type u                                       -- I(有限性は C7/§10 の finite realization 側で付加)
  indexOrder : LinearOrder Index                       -- 添字の全順序
  chart : Index -> S.category                          -- U_i
  inclusion : ∀ i : Index, chart i ⟶ base             -- u_i
  inclusion_mono : ∀ i : Index, CategoryTheory.Mono (inclusion i)
  pairCtx : Index -> Index -> S.category               -- U_ij(全 pair 分を保持)
  pairFst : ∀ i j, pairCtx i j ⟶ chart i
  pairSnd : ∀ i j, pairCtx i j ⟶ chart j
  pairLift : ∀ {i j} {X : S.category},
      (X ⟶ chart i) -> (X ⟶ chart j) -> (X ⟶ pairCtx i j)   -- pullback lift
  tripleCtx : Index -> Index -> Index -> S.category    -- U_ijk
  tripleFaceIJ : ∀ i j k, tripleCtx i j k ⟶ pairCtx i j
  tripleFaceIK : ∀ i j k, tripleCtx i j k ⟶ pairCtx i k
  tripleFaceJK : ∀ i j k, tripleCtx i j k ⟶ pairCtx j k
  tripleLift : ∀ {i j k} {X : S.category},
      (X ⟶ chart i) -> (X ⟶ chart j) -> (X ⟶ chart k) -> (X ⟶ tripleCtx i j k)
  omittedPair : Index -> Index -> Prop                 -- 積から除く empty U_ij の selected 指定
  omittedTriple : Index -> Index -> Index -> Prop      -- 同 U_ijk
```

設計判断:

- **overlap を field に持つ**: `S.overlap : ContextOverlapPullback` は `ArchCtx` 上で
  定義され、site category は quotient である。cover 側に overlap を selected data として
  持ち、`pairLift` / `tripleLift` で pullback 性を要求する形が、既存
  `CoverRelativeCechCover`(simplex / face 明示データ)のイディオムと整合する。
  C1 は `S.overlap` と finite-meet poset model から canonical constructor を与える。
- **`inclusion_mono` は statement 忠実性のための明示前提**: 本文 §1 は一般 `ArchCtx(A)`
  での明示仮定として mono を要求する。現行 Lean site model は thin category なので
  mono は全射に対して成立し、補題2.1A が使う diagonal 同型
  `chart i ≅ pairCtx i i` は `pairLift (𝟙 _) (𝟙 _)` から導出できる。C1 は
  thin model での自動成立を instance / theorem として示す(C1 受け入れ要件4に対応)。
- **empty overlap は selected 指定**: site 層に context の空性述語はないため、
  「積から除く」対象は cover author の selected data である(本文 §1「空の pullback は
  積から除き、その値は定理1.1 の empty-overlap normalization で固定する」)。
  複体(定義2.1)の積は `i < j` かつ `¬ omittedPair i j` の成分のみを走る。
  省略側の値の固定は入力8(§4.8)が supply する。
- 増加添字三項複体 `C⁰/C¹/C²`、`δ⁰/δ¹`、補題2.2、定義2.3 の `H¹`、および
  補題2.1A(`CoverRelativeCechComplex.AdditiveCechH1` との bridge)は C1 の
  generated / proved 成果であり、cover structure の field にしない。

## 4. 定理1.1 の8入力の structure 設計

入力番号と field の対応を先に固定する。

| 定理1.1 入力 | structure | 実装子 |
| --- | --- | --- |
| (1) `M_sem` の生成データ | `SemanticRepairPresentation` | C1 |
| (2) `Q_E` | `CoefficientPresheafData` + C3a realization | C1(generic) / C3a(`Q_E` 固定) |
| (3) 一次写像 χ | `PrimaryCoefficientCorrespondence` | C3 |
| (4) completeness 対 | `RelationComplete` / `GeneratorComplete`(定理仮定 Prop) | C3 / C3a |
| (5) `P_sem` + repair atlas | `AffineSemanticRepairSystem` + `SemanticRepairAtlas` | C2 |
| (6) `P_E` + lift atlas | `AffineCoefficientLiftSystem` + `CoefficientLiftAtlas` | C2 |
| (7) `β : P_sem → P_E` | `PrimaryStateCorrespondence` | C3 |
| (8) empty-overlap normalization | `EmptyOverlapNormalization` | C1(定義)/ 各子(消費) |

### 4.1 入力1: semantic repair presentation(定義3.1)

```lean
/-- X.定義3.1: semantic atom / projection / support / local repair relation。 -/
structure SemanticRepairPresentation {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  SemanticAtom : S.category -> Type u                          -- Λ(V)
  restrictAtom : ∀ {V' V : S.category}, (V' ⟶ V) ->
      SemanticAtom V -> SemanticAtom V'
  restrictAtom_id : ∀ (V) (l : SemanticAtom V), restrictAtom (𝟙 V) l = l
  restrictAtom_comp :
      ∀ {V'' V' V} (f : V'' ⟶ V') (g : V' ⟶ V) (l : SemanticAtom V),
        restrictAtom (f ≫ g) l = restrictAtom f (restrictAtom g l)
  projection : ∀ V, SemanticAtom V -> U.Atom                   -- π_V
  projection_objectFamily :
      ∀ V l, A.configuration.family.mem (projection V l)
  projection_natural : ∀ {V' V} (f : V' ⟶ V) (l : SemanticAtom V),
      projection V' (restrictAtom f l) = projection V l
  supported : ∀ V, SemanticAtom V -> Prop                      -- S(V) ⊆ Λ(V)
  supported_restrict : ∀ {V' V} (f : V' ⟶ V) {l : SemanticAtom V},
      supported V l -> supported V' (restrictAtom f l)
  rel : ∀ V, Set (SupportedWord S V)                           -- Rel_rep(V) ⊆ ℤ^(S(V))
  rel_restrict : ∀ {V' V} (f : V' ⟶ V),
      wordRestrict f '' rel V ⊆ (relSpan V' : Set (SupportedWord S V'))
```

ここで C1 が定義する generated 対象:

```lean
abbrev SupportedAtom (P : SemanticRepairPresentation S) (V) :=
  {l : P.SemanticAtom V // P.supported V l}
abbrev SupportedWord (P) (V) := SupportedAtom P V →₀ ℤ        -- F_sem(V)(定義3.2)
def wordRestrict … : SupportedWord P V →+ SupportedWord P V'   -- Finsupp.mapDomain
def relSpan (P) (V) : AddSubgroup (SupportedWord P V) :=
  AddSubgroup.closure (P.rel V)                                 -- R_rep(V)
def MSem (P) (V) := SupportedWord P V ⧸ relSpan P V             -- M_sem(V)(定義3.2)
```

命題3.3(presheaf 性)と定義3.4(`C_sem`)は C1 の proved / generated 成果である。
`C_sem` の定義は `Q_E`・幾何側複体・comparison map を参照しない(C1 受け入れ要件1)。

- `projection` の値域は `U.Atom` + object family membership とする。本文の
  `At(V)`(occurrence)読みに対し、quotient site category 上で `supportReads` を
  述語化する経路は C1 実装時のレビュー論点として残す。既定は family membership。

### 4.2 入力2: 係数 target(定義5.1 の座)

comparison core(§6–§7)は係数について generic である(本文定義6.1「`Q` を
intersection diagram 上の可換群値 presheaf とする」)。

```lean
/-- 可換群値係数 presheaf。Equation/Basic の明示 restriction イディオムに合わせる。 -/
structure CoefficientPresheafData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  carrier : S.category -> Type u
  addCommGroup : ∀ V, AddCommGroup (carrier V)
  restrict : ∀ {V' V : S.category}, (V' ⟶ V) -> carrier V →+ carrier V'
  restrict_id : ∀ (V) (x : carrier V), restrict (𝟙 V) x = x
  restrict_comp : ∀ {V'' V' V} (f : V'' ⟶ V') (g : V' ⟶ V) (x : carrier V),
      restrict (f ≫ g) x = restrict f (restrict g x)
```

`Q_E` の固定(入力2の実体)は C3a が行う:

```lean
/-- X.定義5.1: E から生成される Q_E = O_E / I_Ob^E。 -/
def equationCoefficient (S : Site.AATSite A) : CoefficientPresheafData S where
  carrier V := S.equationSystem.ObstructionQuotient V
  restrict f := (S.equationSystem.obstructionQuotientRestrict f).toAddMonoidHom
  …
```

`ObstructionQuotient` / `obstructionQuotientRestrict`
(`Formal/AG/LawAlgebra/LawEquation.lean:108,114`)は既存 declaration であり、
#3734 の移行を待たずに使える(#3757 備考の「既存 equation-system API で閉じる」)。

### 4.3 入力3: primary coefficient correspondence(定義6.1)

```lean
/-- X.定義6.1: supported semantic atom を係数へ送る restriction-natural な一次写像。 -/
structure PrimaryCoefficientCorrespondence
    (P : SemanticRepairPresentation S) (Q : CoefficientPresheafData S) where
  chi : ∀ V, SupportedAtom P V -> Q.carrier V                  -- χ_V
  chi_natural : ∀ {V' V} (f : V' ⟶ V) (l : SupportedAtom P V),
      Q.restrict f (chi V l) = chi V' (restrictSupported P f l)
```

free abelian group 上への延長 `chiHom V : SupportedWord P V →+ Q.carrier V`
(`Finsupp` の普遍性)は C3 の generated 成果である。

### 4.4 入力4: completeness 対(定義6.2 の第2・第3条件)

```lean
def RelationComplete (χ …) (V : S.category) : Prop :=
  ∀ x : SupportedWord P V, chiHom χ V x = 0 -> x ∈ relSpan P V
def GeneratorComplete (χ …) (V : S.category) : Prop :=
  ∀ q : Q.carrier V, ∃ x : SupportedWord P V, chiHom χ V x = q
```

これらは定理6.3・系6.7 が「cover intersection ごとに」仮定として受け取る
検証可能条件であり、structure の常設 field にしない。quantify 対象は
`𝒰` の intersection context(chart、非省略 pair、非省略 triple)である。
第1条件(repair-relation soundness)は入力にせず、補題6.2A(C3)が
入力5–7 から導出する。

### 4.5 入力5: affine semantic repair system + atlas(定義4.1・4.2)

```lean
/-- X.定義4.1: F_sem 作用つき semantic local repair state と3条件。 -/
structure AffineSemanticRepairSystem (P : SemanticRepairPresentation S) where
  State : S.category -> Type u                                 -- P_sem(V)
  restrictState : ∀ {V' V}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : …
  restrictState_comp : …
  act : ∀ V, SupportedWord P V -> State V -> State V           -- x + p
  act_zero : ∀ V (p : State V), act V 0 p = p
  act_add : ∀ V x y (p : State V), act V (x + y) p = act V x (act V y p)
  act_restrict : ∀ {V' V} (f : V' ⟶ V) x (p : State V),
      restrictState f (act V x p) = act V' (wordRestrict f x) (restrictState f p)
  relation_sound : ∀ V x, x ∈ relSpan P V -> ∀ p, act V x p = p
  stabilizer_complete : ∀ V (p : State V) x, act V x p = p -> x ∈ relSpan P V
  transitive : ∀ V (p q : State V), ∃ x, q = act V x p

/-- X.定義4.2: selected local repair atlas。 -/
structure SemanticRepairAtlas (𝒰 : MonomorphicOrderedCover S)
    (Psem : AffineSemanticRepairSystem P) where
  localRepair : ∀ i : 𝒰.Index, Psem.State (𝒰.chart i)          -- p_i
```

- `stabilizer_complete` の非空性前提は witness `p` 自身が担う(本文の
  「`P_sem(V)` が非空で `x+p=p` なら」の忠実な読み)。
- semantic faithfulness は本文どおり定理として導出する(定義4.1 の注記)。field にしない。
- residual cochain `r_sem`(定義4.2)は atlas の差から C2 が生成する。
  `r_sem` を selected `1`-cocycle として供給しない(縮小禁止)。

### 4.6 入力6: `Q`-controlled lift system + atlas(定義5.3)

```lean
/-- X.定義5.3: Q が作用する equation-lift local state。 -/
structure AffineCoefficientLiftSystem (Q : CoefficientPresheafData S) where
  State : S.category -> Type u                                 -- P_E(V)
  restrictState : … (id / comp 律つき)
  act : ∀ V, Q.carrier V -> State V -> State V
  act_zero / act_add / act_restrict : …
  free : ∀ V (e : State V) q, act V q e = e -> q = 0
  transitive : ∀ V (e e' : State V), ∃ q, e' = act V q e

/-- X.定義5.3: selected local equation-lift atlas。 -/
structure CoefficientLiftAtlas (𝒰) (PQ : AffineCoefficientLiftSystem Q) where
  localLift : ∀ i : 𝒰.Index, PQ.State (𝒰.chart i)              -- e_i
```

`r_E` は atlas の差から C2 が生成する(補題5.4 は C2 の proved 成果)。

### 4.7 入力7: primary state correspondence(定義6.1B)

```lean
/-- X.定義6.1B: restriction-natural かつ generator-equivariant な β。 -/
structure PrimaryStateCorrespondence
    (χ : PrimaryCoefficientCorrespondence P Q)
    (Psem : AffineSemanticRepairSystem P)
    (PQ : AffineCoefficientLiftSystem Q) where
  beta : ∀ V, Psem.State V -> PQ.State V                       -- β_V
  beta_natural : ∀ {V' V} (f : V' ⟶ V) (p : Psem.State V),
      PQ.restrictState f (beta V p) = beta V' (Psem.restrictState f p)
  beta_equivariant : ∀ V (l : SupportedAtom P V) (p : Psem.State V),
      beta V (Psem.act V (Finsupp.single l 1) p) =
        PQ.act V (χ.chi V l) (beta V p)
```

equivariance は generator 水準のみ入力とする(有限和・inverse への延長は作用則から
従う: 本文定義6.1B)。`β` の逆写像・全単射性は field にしない(系6.5 の結論)。

### 4.8 入力8: empty-overlap normalization

```lean
/-- X.§1 入力8: 積から除いた empty intersection 上の値の固定。 -/
structure EmptyOverlapNormalization (𝒰 : MonomorphicOrderedCover S)
    (P : SemanticRepairPresentation S) (Q : CoefficientPresheafData S)
    (Psem : AffineSemanticRepairSystem P)
    (PQ : AffineCoefficientLiftSystem Q) where
  msem_pair_trivial : ∀ {i j}, 𝒰.omittedPair i j ->
      ∀ x : MSem P (𝒰.pairCtx i j), x = 0
  q_pair_trivial : ∀ {i j}, 𝒰.omittedPair i j ->
      ∀ x : Q.carrier (𝒰.pairCtx i j), x = 0
  psem_pair_subsingleton : ∀ {i j}, 𝒰.omittedPair i j ->
      Subsingleton (Psem.State (𝒰.pairCtx i j))
  pQ_pair_subsingleton : ∀ {i j}, 𝒰.omittedPair i j ->
      Subsingleton (PQ.State (𝒰.pairCtx i j))
  -- omittedTriple に対する同形の4 field(msem/q trivial、Psem/PQ subsingleton)
```

normalization は selected datum として structure に現れ、導出や省略で置換しない
(C1 受け入れ要件4)。消費箇所は補題2.1A(C1)と定理8.2 の matching family 化(C5)。

### 4.9 入力 bundle と equation realization

```lean
/-- X.定理1.1: 8入力 + monomorphic cover の bundle。定理7.6 系の主語。 -/
structure SagaComparisonInputs (S : Site.AATSite A) where
  cover : MonomorphicOrderedCover S
  presentation : SemanticRepairPresentation S                   -- 入力1
  coefficient : CoefficientPresheafData S                       -- 入力2
  correspondence : PrimaryCoefficientCorrespondence presentation coefficient  -- 入力3
  repairSystem : AffineSemanticRepairSystem presentation        -- 入力5a
  repairAtlas : SemanticRepairAtlas cover repairSystem          -- 入力5b
  liftSystem : AffineCoefficientLiftSystem coefficient          -- 入力6a
  liftAtlas : CoefficientLiftAtlas cover liftSystem             -- 入力6b
  stateCorrespondence :
    PrimaryStateCorrespondence correspondence repairSystem liftSystem  -- 入力7
  normalization : EmptyOverlapNormalization …                   -- 入力8
```

入力4(completeness 対)は bundle に入れず、定理仮定として各 intersection 上で
受け取る(§4.4)。C3a の equation realization は次で `Q := Q_E` を固定する:

```lean
/-- X.命題6.1A: λ ↦ (i_λ, A_λ, π(λ)) の selected 対応。 -/
structure EquationSemanticRealization (P : SemanticRepairPresentation S) where
  lawIndex : ∀ V, SupportedAtom P V -> S.equationSystem.Index          -- i_λ
  lawIndex_required : ∀ V l, S.equationSystem.Required (lawIndex V l)
  archReading : ∀ V, SupportedAtom P V -> ArchitectureObject U         -- A_λ
  lawIndex_natural / archReading_natural : restriction との可換
```

`χ^E_V(λ) := [ε_{V,A_λ,i_λ,π_V(λ)}]` は `equationResidual` +
`Ideal.Quotient.mk` から C3a が構成し、naturality は
`equationResidual_restrict` + `obstructionQuotientRestrict_mk` で証明する。

## 5. field にしないもの(縮小禁止リスト対応)

次は定理の結論または generated 対象であり、いかなる structure の field にもしない。

- `Φ` とその逆写像、`Φ` の同型性(定理6.3 の結論)
- `κ^n` と微分可換性(定義7.1 は generated、定理7.2 は proved)
- `r_sem` / `r_E` の cocycle 性(補題4.3・補題5.4 の結論)、`r_sem`・`r_E` 自体
  (atlas の差から generated)
- `H¹` 同型・residual class 対応・Nonempty 同値(定理7.4–7.6・定理8.2 の結論)
- repair-relation soundness(補題6.2A が入力5–7 から導出)
- semantic faithfulness(定義4.1 の注記どおり定理)
- `β` の全単射性(系6.5 の結論)
- per-cover amalgamation map(定義8.1「別データとして置かない」。C5 は
  `S_X` topology 上の sheaf condition から `𝒰` に対する条件を導出する)
- `r_sem` を幾何側 residual の逆像として定義しない(縮小禁止リスト)

本文が量化する一般対象に対して入力を強めない。特に `Index` の有限性は
comparison core(定理6.3–8.2)の入力にせず、finite realization(§10、C7)の側で付加する。

## 6. 旧 `Formal/AG/SemanticRepair/*` の存廃仮決め(R0-2)

区分は4種。最終処分はすべて C8(#3769)が裁定し、AxiomAudit 収載
(`Formal/AG/AxiomAudit.lean`)と fixture(`Formal/AG/Examples/SemanticRepairPart10*.lean`)の
更新を伴う。本 Issue 樹の C1–C7 は「凍結」区分へ新規依存を作らない。

| 区分 | 意味 |
| --- | --- |
| 維持 | 新 route と競合しない資産。そのまま保持 |
| reuse | 新 route が proof pattern / bridge 素材として参照する |
| 置換候補 | C1–C5 の generated 構成が同役割を提供した後、C8 が新旧対応表を作って退役を裁定 |
| 凍結 | G-06 production route 端点。#3716/#3734 の移行対象。新規依存禁止 |

### AdditiveH1.lean

| 宣言 | 仮決め |
| --- | --- |
| `SemanticRepairCover`, `toCoverNerve`, `SemanticRepairCoverCechData`, `SemanticRepairCoverCechRealization`, `ResidualFacewiseCocycle`, `residualFacewiseCocycle`, `AdditiveRepairCoverContext`, `Supports`, `Restrict`, `SelectedRepairCoverDescentSelection`, `SemanticRepairCover.toDescentSelection`, `CechZ1`, `CechB1`, `SemanticRepairAdditiveCechH1Data`, `Cocycle`, `Cohomologous`, `cohomologous_refl/symm/trans`, `setoid`, `H1`, `residualClass`, `zeroClass`, `H1Zero`, `h1Zero_iff_boundary`, `semanticRepairAdditiveH1Zero_iff_boundary` | 置換候補(C1 の増加添字複体 + 定義2.3 `H¹` が同役割) |
| `SemanticRepairCoverH1BoundaryRelationAbelianData`, `SemanticRepairCoverH1FaithfulnessData`, `GlobalRepairCoherent`, `zero1_is_boundary`, `globalRepairCoherent_of_boundary`, `SemanticRepairCoverH1AdditiveFaithfulnessData`, `toFaithfulnessData`(2箇所), `toAdditiveCechH1Data`(2箇所), `globalRepairCoherent_of_additiveH1Zero`(2箇所), `toFiniteGluingComplex`, `semanticFaithfulnessHypotheses`, `toFaithfulnessData_globalRepairCoherent_iff`, `SemanticRepairCoverH1BoundaryRelationAdditiveData`, `toAdditiveFaithfulnessData` | 置換候補(C2 定義4.1 の relation_sound / stabilizer_complete / transitive が supplied faithfulness 系を置換) |
| `TrueSheafConditionCertificate` | 置換候補(C5 定義8.1 は per-cover certificate を置かず topology-wide sheaf condition から導出) |
| `AdditiveRepairSolution`, `additiveRepairGaugeSubgroup`, `AdditiveRepairGauge`, `additiveRepairGaugeAddCommGroup`, `AdditiveRepairPrimitiveTranslation`, `additiveRepairPrimitiveTranslation`, `additiveRepairGaugeBetween`, `additiveRepairGaugeAction`, `additiveRepairGaugeAddAction`, `additiveRepairGaugeAction_zero/_add`, `additiveRepairGaugeBetween_action`, `additiveRepairGaugeAction_free`, `AdditiveRepairGaugeActsSimplyTransitively`, `additiveRepairGaugeActsSimplyTransitively`, `additiveRepairSolution_of_h1Zero`, `additiveRepairSolution_nonempty_iff_h1Zero`, `AdditiveTorsorTrivial`, `additiveTorsorTrivial_of_additiveH1Zero` | reuse(C2 torsor・C5 effectivity の proof pattern)→ C8 で退役裁定 |
| `SelectedHigherCoherenceDefect`, `SelectedHigherCoherenceTrivialization`, `HigherCoherenceVanishes`, `selectedHigherCoherenceTrivialization_of_additive`, `selectedHigherCoherence_facewise`, `higherCoherenceVanishes_of_additive`, `additiveRepairCoverStackBase`, `AdditiveFiberTranslation`, `additiveFiberTranslation`, `additiveFiberTranslation_unique`, `additiveRepairCoverTranslationPresheaf`, `residualTransition_eq_localDifference`, `selectedRepairLocalObjects`, `selectedRepairDescentDatum`, `selectedRepairEffectiveDescent_of_h1Zero`, `StackEffectivelyVanishes`, `stackEffectivelyVanishes_of_additive`, `selectedHigherCoherenceAndEffectiveDescent_of_additive`, `coverSheafConditionFor_of_trueSheafCertificate`, `coverDescent_of_trueSheafCertificate`, `globalRepairCoherent_iff_additiveH1Zero` | 維持(原則8.4 の higher / stack 面。新 route のスコープ外) |
| `SemanticRepairAdditiveFiniteComparison`, `finiteShadow_obstructionVanishes_of_coverBoundary`, `coverBoundary_of_finiteShadow_obstructionVanishes`, `additiveH1Zero_iff_finiteShadow_obstructionVanishes`, `finiteShadowComparison_package`, `SemanticRepairCoverRefinement`, `SemanticRepairAdditiveRefinementComparison`, `refinement_boundary_pullback`, `refinement_additiveH1Zero_pullback`, `refinementPullback_package`, `trueSheafH1SemanticRepairGluing_boundaryRelationAdditive_package` | 維持(有限比較・refinement。C7 の比較材料) |

### Bootstrap.lean

`UsesAATSite` ほか `Uses*` abbrev 群、`PrerequisiteStatus`、`PartXDependencyStatus`、
`currentDependencyStatus`、`current_*_available` 定理群 — **維持**(可用性面。
C8 で新 route 完成後の status 更新のみ)。

### Boundary.lean

`generatedSAGA_lawIndependentConclusions_withoutLawPremise`,
`SemanticRepairTypedComparisonTarget`, `SemanticRepairTypedZeroComparison`,
`typedZeroComparison_preserves_zero`,
`typedComparisonTarget_not_unconditional_for_emptyTarget`,
`typedComparisonTarget_carrier_nonuniformity_punit_zmod2`,
`SemanticRepairRefinementZeroComparison`, `refinementZeroComparison_preserves_zero`,
`refinementZeroComparison_blocks_coarseZero_fineNonzero`,
`refinementZeroComparison_not_unconditional_for_coarseZero_fineNonzero` —
**維持**(no-go 境界資産。#3242 裁定(C8)の一次材料)。

### Examples.lean / GluingComplex.lean

- Examples.lean 全宣言(`VisibleLocalCoherent` 〜 `finiteSemanticRepairGluingDescent_iff`)—
  **維持**(negative fixture。AxiomAudit 収載)。
- GluingComplex.lean 全宣言(`FiniteSemanticRepairGluingComplex` 〜
  `finiteSemanticRepairGluingDescent_package`、`CompleteSupportBoundaryComplex` 系、
  `FullFiniteSemanticRepairGluingComplex` 系)— **置換候補**(C2/C5 の generated 構成が
  同役割)。ただし AxiomAudit・Examples の依存が深いため、退役は C8 が audit / fixture
  込みで裁定する。

### H1Comparison.lean

全宣言(`SemanticRepairAdditiveH1Surface` 〜
`semanticRepairAdditiveH1_coverRelativeH1_comparison_package`)— **置換候補**。
補題2.1A(C1)が増加添字複体と第IV部複体の `Z¹/B¹/H¹` 同型を与えた後、
旧 additive H1 surface 経由の比較は新 bridge に一本化する。
`semanticRepairAdditiveH1_addEquiv_additiveCechH1` の実装は C1 bridge の
reuse pattern を兼ねる。

### LawEquationGeneratedPair.lean / SagaComparison.lean

全宣言 — **凍結**(G-06 production route。#3716/#3734 の移行対象、C8 で台帳同期)。
C3a は命題6.1A・系6.7 を §4.9 の設計で既存 equation-system API から独立に閉じ、
この2ファイルへの依存も重複実装も作らない。

### Projection.lean

- `SemanticAtomProjection`, `Support` — **reuse**(定義3.1 `projection` の先行素材。
  新 route は独立定義し、C8 で対応を記録)。
- `FiniteSemanticRepairCoverDatum`, `SemanticProjectedResidual`,
  `semanticProjectedResidual_iff_holonomySupport`, `SemanticRepairClosed`,
  `ResidualComponentCoveredSupport`, `ResidualComponentFaithfulSupport`,
  `semanticRepairClosed_iff_residualComponentCovered_and_faithful` — **凍結**
  (G-06 依存面)。
- fixture 群(`Atom`, `Component`, `projection`, `cover`, `support`,
  `support_residualComponentCovered`, `support_not_residualComponentFaithful`,
  `support_not_semanticRepairClosed`, `covered_not_faithful_not_closed`,
  `coverageWithoutFaithfulness_covered_not_faithful_not_closed`)— **維持**。

### SiteCech.lean

- `atomGeneratedCoverage_generates_AATGrothendieckTopology`,
  `selectedAATSiteTopology_eq_atomGeneratedGrothendieckTopology` — **維持**
  (site 接続定理。新 route も参照可)。
- `SemanticRepairCoverRelativeCoverBridge`, `toCoverRelativeCechCover`,
  `EmptyIndexZeroSimplexIncidenceNoGo`, `no_incidence`,
  `no_constructor_from_coverBridge_without_zeroSimplexChartIncidence`,
  `chartIndexedZeroCover_constructs_zeroSimplexChartIncidence`,
  `coverNerve_typedComponent_adequacy`,
  `aatSheafCondition_coverMembership_descent_effectiveGluing` — **reuse**
  (補題2.1A の bridge・C5 sheaf condition 接続の素材)。

### 外部依存ファイル

- `Formal/AG/Examples/SemanticRepairPart10.lean`(4024行)/
  `SemanticRepairPart10SiteGeometry.lean` — **凍結**(旧 route fixture)。
  C7 の circle witness(例10.2 / 付録B.9)は新規に作り、旧 fixture を流用しない。
- `Formal/AG/AxiomAudit.lean` の SemanticRepair 収載行 — 維持。C8 で新旧対応表を反映。

## 7. G-07 対応表の採用(R0-3)

#3757 本文の G-07 対応表を R0 の固定 map として採用する。全 16 declaration の実在と
所在を検証済み:

| G-07 declaration | 所在(検証済み) | 扱い |
| --- | --- | --- |
| `PatchReadingSource` | `research/lean/ResearchLean/AG/QualitySurface/LawGeneratedSemanticFirstOrderRepair.lean:81` | generalize |
| `OverlapLawCombination` | 同 `:158` | generalize |
| `evaluateCombination_mem_obstructionIdeal` | 同 `:191` | reuse pattern |
| `rawQ0_pair_compatible` | 同 `:214` | specialization |
| `LocalLiftData` | `…/LawGeneratedLargeConormalDescent.lean:101` | reuse |
| `localLiftDifferenceFor` | `…/LawGeneratedConormalDescent.lean:352` / `…LargeConormalDescent.lean:234` | reuse |
| `localLiftDifferenceFor_cocycle` | 同 `:369` / `:249` | reuse |
| `connectingClass_choice_independent` | 同 `:447` / `:330` | reuse |
| `correctedLocalLiftCochain_d_eq_zero` | 同 `:658` / `:541` | reuse |
| `amalgamatedCorrectedLocalLift` | 同 `:849` / `:711` | reuse |
| `connectingClassFor_isZero_iff_nonempty_globalLift` | `…LargeConormalDescent.lean:779` | reuse |
| `SemanticFirstOrderRepair` | `…/LawGeneratedSemanticFirstOrderRepair.lean:737` | specialization |
| `SemanticFirstOrderRepairEquiv` | 同 `:863` | specialization |
| `connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair` | 同 `:872` | specialization |
| `lawGeneratedConormalFirstOrderDescent_package` | `…/LawGeneratedConormalFirstOrderDescentPackage.lean:239` | specialization |

import 経路も #3757 の記載どおりであることを確認した:
`LawGeneratedLargeCoefficientCech.lean` の `Formal/AG` 側 import は generic な
`Formal.AG.Cohomology.CochainComparison`(+ `Site.FinitePosetGeometry`)のみで、
`SemanticRepairCechGrounding` / `SagaComparison` / `H1Comparison` を import しない
(非循環)。

運用は #3757 記載のとおり: reuse / generalize 分は C1–C5 の構成で proof pattern
として使い、C6(#3767)で `Formal/` へ蒸留する。specialization 分は C6 が
first-order conormal instance として固定する。蒸留は本体内での再構成であり、
`ResearchLean` の import ではない(`docs/aat/guideline.md`「移植 ≠ import」)。

## 8. C1–C8 への引き渡し

| 子 | 本 note の対応節 | 実装する generated / proved 対象 |
| --- | --- | --- |
| C1 #3762 | §3, §4.1, §4.2(generic), §4.8 | 増加添字三項複体、補題2.1A bridge、`F_sem`/`R_rep`/`M_sem`、命題3.3、定義3.4、mono 自動成立 instance |
| C2 #3763 | §4.5, §4.6 | torsor 帰結(freeness / faithfulness)、`r_sem`/`r_E` 生成、補題4.3–系4.5、補題5.4 |
| C3 #3764 | §4.3, §4.4, §4.7 | `chiHom`、補題6.2A、定理6.3、系6.4–6.5、例6.6 negative fixture |
| C3a #3771 | §4.2(realization), §4.9 | `equationCoefficient`、`EquationSemanticRealization`、命題6.1A、系6.7 |
| C4 #3765 | §5 | `κ^n`、定理7.2–7.6 |
| C5 #3766 | §5, §4.8 | 定義8.1(topology-wide sheaf condition)、定理8.2、系8.3 |
| C6 #3767 | §7 | G-07 蒸留 + conormal specialization |
| C7 #3768 | §3(有限性付加) | circle witness(例10.2 / 付録B.9)、#3718 吸収 |
| C8 #3769 | §6 | 存廃裁定の最終化、#3242 裁定、AxiomAudit / fixture / 台帳同期 |

signature の細部(implicit 引数の形、`Finsupp` の具体 API、abbrev / def の別)は
実装子が調整してよい。ただし入力番号と field の対応(§4 冒頭表)、§5 の
「field にしないもの」、§6 の凍結区分への新規依存禁止を変更する場合は、
本 note を更新し子 PR で明記する。
