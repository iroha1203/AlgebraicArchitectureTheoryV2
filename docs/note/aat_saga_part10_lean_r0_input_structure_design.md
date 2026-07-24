# SAGA 中心定理 Lean 形式化 R0: 入力 structure 設計(Issue #3757)

status: R0 fixed(本 note が #3757 R0 の固定成果物。R1 改訂: PR #3775 レビュー finding 1–7 反映。R2 改訂: 敵対セルフレビュー4並列の finding 反映。R3 改訂: 再レビュー残余 F2/F3 反映。R4 改訂: C1 実装(#3788)の bridge 形状を反映)
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
C1–C8 が本文 §9 依存図に整合する import / proof 依存(§2 の線形化)で構成でき、かつ
縮小禁止リスト(同値・逆写像・微分可換性・cocycle 性・`H¹` 同値の certificate field 化禁止)を
構造的に満たせるか。

## 1. 基底設定と既存資産の接続点

新 route は次の既存 declaration を接続点として使う。いずれも実在を確認済み。

| 接続点 | 場所 | 役割 |
| --- | --- | --- |
| `Site.AATSite` | `Formal/AG/Site/Geometry.lean:18` | site 全体(contextPreorder / equationSystem / overlap / topology)。新 structure 群の基底 |
| `Site.ContextCategoryObject` | `Formal/AG/Site/ContextCategory.lean:80` | site category の対象。`ctx : ArchCtx A` の素朴な wrapper なので `V.ctx.Support` / `supportReads` へ直接アクセスできる |
| `Site.ContextOverlapPullback` | `Formal/AG/Site/ContextCategory.lean:529` | II.仮定4.3 の overlap package。cover の `U_ij` / tuple overlap 生成の canonical 供給源(§3.3) |
| `Site.AATSite.topology` | `Formal/AG/Site/Geometry.lean:39` | 生成 Grothendieck topology `J_E`。定義8.1 条件3 の membership の座(§3.2) |
| `Cohomology.CoverRelativeCechCover` / `CoverRelativeCechComplex` | `Formal/AG/Cohomology/CechComplex.lean` | 第IV部の全 ordered tuple 複体。補題2.1A の比較先(`AdditiveCechH1` 面) |
| `ArchitecturalEquationSystem` | `Formal/AG/Equation/Basic.lean:42` | equation system `E`(Part I 定義7.1–7.3) |
| `ArchitecturalEquationSystem.ObstructionQuotient` / `obstructionQuotientRestrict` | `Formal/AG/LawAlgebra/LawEquation.lean:108,114` | `Q_E(V) = O_E(V)/I_Ob^E(V)` と restriction(Part III 定理11.4 の Lean 実体)。C3a の realization target |
| `Site.FinitePoset` 系(第II部 命題4.2 model) | `Formal/AG/Site/FinitePoset.lean` ほか | mono 自動成立 instance と canonical constructor の供給源(C1) |

site category は thin category である(`ContextCategoryObject` の `Preorder` instance)。
したがって射の等式・図式可換は自動で成立し、新 structure 群は morphism データと
lift データだけを持てばよい。

### universe 規約

G-07 の大係数資産(conormal lift / state に `Type (u+1)` の実体がある。§7)を C6 で
蒸留 map どおりに受けるため、新 structure 群は site universe `u` と係数・状態 universe を
分離した universe-polymorphic signature で固定する。旧 route の
`SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z}` と同じ流儀である。

```text
u : site(AtomCarrier / S.category / occurrence)
v : semantic atom carrier(Λ(V))
w : 係数 carrier(Q / M_sem の比較先)
x : semantic state carrier(P_sem)
y : lift state carrier(P_E)
```

以下の signature はこの規約で書く。`Type (u+1)` の係数・状態は `w` / `x` / `y` の
instantiation として受ける。

## 2. 配置と namespace

新 route は既存 G-06 route(§6)と衝突しない新 subtree に置く。

```text
namespace: AAT.AG.SemanticRepair.Saga

Formal/AG/SemanticRepair/Saga/Cover.lean            -- C1: §3(cover / Int / bridge)
Formal/AG/SemanticRepair/Saga/Presentation.lean     -- C1: 定義3.1–3.4(M_sem)
Formal/AG/SemanticRepair/Saga/RepairTorsor.lean     -- C2: 定義4.1–系4.5
Formal/AG/SemanticRepair/Saga/EquationLift.lean     -- C2: 定義5.3–補題5.4
Formal/AG/SemanticRepair/Saga/Exactness.lean        -- C3: 定義6.1–例6.6(Φ)
Formal/AG/SemanticRepair/Saga/EquationRealization.lean -- C3a: 命題6.1A・系6.7
Formal/AG/SemanticRepair/Saga/CochainComparison.lean   -- C4: 定義7.1–定理7.6(κ, H¹)
Formal/AG/SemanticRepair/Saga/TrueSheafDescent.lean    -- C5: 定義8.1–系8.3
Formal/AG/SemanticRepair/Saga/CircleWitness.lean       -- C7: 例10.2 / 付録B.9
```

ファイル分割は実装時に多少調整してよいが、§9 依存図に整合する import 依存
(線形化 C1 ← C2 ← C3 ← C3a ← C4 ← C5、C7 は C4 後。§9 の cross 依存、
例えば定理7.5 → 補題4.3 / 補題5.4 は推移的 import で充足する)を壊す統合はしない。

## 3. Cover 層の structure 設計

cover 層は3段で固定する。generic core(§2–§7 が使う)、topology 接続
(定義8.1・定理8.2 が使う)、有限 specialization(定理1.1 の最終 statement が使う)である。

### 3.1 Monomorphic ordered cover(generic core)

```lean
/-- X.§1: 全順序添字つき monomorphic AAT cover。
overlap は selected data として持ち、pullback 性は lift field で持つ
(thin category なので可換条件と一意性は自動)。 -/
structure MonomorphicOrderedCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) : Type (u + 1) where
  base : S.category                                    -- W
  Index : Type u                                       -- I
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
  omittedTriple_mono :
      ∀ i j k, indexOrder.lt i j -> indexOrder.lt j k -> ¬ omittedTriple i j k ->
        ¬ omittedPair i j ∧ ¬ omittedPair i k ∧ ¬ omittedPair j k
```

設計判断:

- **`inclusion_mono` は本文 §1 の明示前提**。現行 site model は thin なので mono は
  全射に対して成立し、補題2.1A が使う diagonal 同型 `chart i ≅ pairCtx i i` は
  `pairLift (𝟙 _) (𝟙 _)` から導出できる。C1 は thin model での自動成立を
  instance / theorem として示す(C1 受け入れ要件4、第II部 命題4.2 model の読み)。
- **empty overlap は selected 指定**。site 層に context の空性述語はないため、
  「積から除く」対象は cover author の selected data である(本文 §1)。省略側の
  値の固定は入力8(§4.8)が supply する。
- **省略指定の単調性**(`omittedTriple_mono`): 本文では
  `U_ijk = U_i ×_W U_j ×_W U_k ⊆ U_ij` により非空 triple の3つの pairwise overlap は
  非空である。この幾何を selected 指定へ忠実に写す条件であり、非省略 triple に対する
  `Face.tripleIJ/IK/JK` の3 face が常に構成可能であること(補題2.2・定理7.2 の
  differential の total 性)を保証する。
- 増加添字三項複体、補題2.2、定義2.3 の `H¹`、補題2.1A は C1 の generated / proved
  成果であり、cover structure の field にしない。

### 3.2 Intersection diagram `Int_{≤2}(𝒰)` と topology 接続

本文の定義6.1・命題6.1A・定義6.1B は係数・対応・local state を
**cover intersection diagram 上で**量化する。site 全域を量化対象にすると本文にない premise の追加になるため、
intersection diagram を型として固定し、§4 の入力3・4・6・7 はこの上で定義する。

```lean
/-- X.定義3.1 注記の Int_{≤2}(𝒰): chart、非省略 pairwise overlap、非省略 triple overlap。 -/
inductive IntersectionIndex {S : Site.AATSite A} (𝒰 : MonomorphicOrderedCover S) where
  | chart (i : 𝒰.Index)
  | pair (i j : 𝒰.Index) (hij : 𝒰.indexOrder.lt i j) (hkeep : ¬ 𝒰.omittedPair i j)
  | triple (i j k : 𝒰.Index) (hij : 𝒰.indexOrder.lt i j) (hjk : 𝒰.indexOrder.lt j k)
      (hkeep : ¬ 𝒰.omittedTriple i j k)

/-- 各 intersection index の実 context。 -/
def IntersectionIndex.ctx : IntersectionIndex 𝒰 -> S.category
  | .chart i => 𝒰.chart i
  | .pair i j _ _ => 𝒰.pairCtx i j
  | .triple i j k _ _ _ => 𝒰.tripleCtx i j k

/-- Int_{≤2}(𝒰) の生成射(face)。restriction はこれに沿ってだけ要求する。 -/
inductive Face {S : Site.AATSite A} (𝒰 : MonomorphicOrderedCover S) :
    IntersectionIndex 𝒰 -> IntersectionIndex 𝒰 -> Type u where
  | pairLeft  (i j hij hkeep) : Face 𝒰 (.pair i j hij hkeep) (.chart i)
  | pairRight (i j hij hkeep) : Face 𝒰 (.pair i j hij hkeep) (.chart j)
  | tripleIJ (i j k hij hjk hkeep) (hkeepP : ¬ 𝒰.omittedPair i j) :
      Face 𝒰 (.triple i j k hij hjk hkeep) (.pair i j hij hkeepP)
  | tripleIK (i j k hij hjk hkeep) (hkeepP : ¬ 𝒰.omittedPair i k) :
      Face 𝒰 (.triple i j k hij hjk hkeep)
        (.pair i k (@lt_trans _ 𝒰.indexOrder.toPartialOrder.toPreorder _ _ _ hij hjk)
          hkeepP)
  | tripleJK (i j k hij hjk hkeep) (hkeepP : ¬ 𝒰.omittedPair j k) :
      Face 𝒰 (.triple i j k hij hjk hkeep) (.pair j k hjk hkeepP)

/-- face の実 site 射(pairFst / pairSnd / tripleFace* を読む)。 -/
def Face.hom : Face 𝒰 σ τ -> (σ.ctx ⟶ τ.ctx)

/-- V が intersection context であること(P_sem の torsor 律の量化域)。 -/
def IsIntersectionCtx (𝒰 : MonomorphicOrderedCover S) (V : S.category) : Prop :=
  ∃ σ : IntersectionIndex 𝒰, σ.ctx = V
```

triple の pair face は非省略 pair を仮定に持つ。この仮定は `omittedTriple_mono`
(§3.1)により非省略 triple に対して常に放電できる。省略 pair へ落ちる restriction
成分は複体に現れず(定義2.1 の積は非省略成分のみ)、その値は入力8 が零に固定する。
なお `indexOrder` は field なので `lt_trans` の dot-notation は解決されない。
inductive の index 式内では上記のとおり明示 term
(`@lt_trans _ 𝒰.indexOrder.toPartialOrder.toPreorder …`)を使う(コンパイル確認済み)。

topology 接続(定義8.1 条件3「`𝒰` がその topology の cover」)は C5 が使う
extension として固定する:

```lean
/-- X.定義8.1 条件3: 生成 topology に属する monomorphic AAT cover。 -/
structure TopologicalMonomorphicCover {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) extends MonomorphicOrderedCover S where
  mem_topology :
    Sieve.generate (Presieve.ofArrows toMonomorphicOrderedCover.chart
        toMonomorphicOrderedCover.inclusion) ∈
      S.topology toMonomorphicOrderedCover.base
```

comparison core(定理6.3–7.6)はこの extension を受け取らない(本文 §7 末尾
「global sheaf condition … は定理7.2–7.6 の仮定ではない」)。定理8.2・系8.3 だけが受け取る。

有限 specialization: 本文 §1 は中心定理のために有限添字集合 `I` を固定する。
定理1.1 の名を持つ最終 statement(C4 の定理7.6 packet と C5 の定理8.2 を束ねる surface)は
`[Fintype 𝒰.Index]` を仮定に持つ。generic core(定理6.3–8.2 の各定理)は
有限性を受け取らない(本文 §1「比較 core 自体には有限性は要らない」、§10)。

### 3.3 canonical constructor と第IV部複体への bridge

C1 は次の2つを固定 signature として実装する。

```lean
/-- S.overlap(ContextOverlapPullback)から pair/triple/tuple overlap を生成する
canonical constructor。finite-meet poset model では mono も自動放電される。 -/
def MonomorphicOrderedCover.ofOverlapPackage
    (base : S.category) (Index : Type u) (indexOrder : LinearOrder Index)
    (chart : Index -> S.category) (inclusion : ∀ i, chart i ⟶ base)
    (inclusion_mono : ∀ i, CategoryTheory.Mono (inclusion i))
    (omittedPair : Index -> Index -> Prop)
    (omittedTripleExtra : Index -> Index -> Index -> Prop) :
    MonomorphicOrderedCover S
  -- pairCtx i j := S.overlap.overlap base.ctx (chart i).ctx (chart j).ctx の wrap、
  -- tripleCtx は左結合の iterated overlap。lift は overlap_lift から。
  -- omittedTriple i j k :=
  --   omittedPair i j ∨ omittedPair i k ∨ omittedPair j k ∨ omittedTripleExtra i j k
  -- と生成するため、omittedTriple_mono は De Morgan で構成的に成立する。
  -- pair が全て非省略で triple だけ空になる cover は omittedTripleExtra で指定する。
  -- 省略指定と実際の空性の結び付けは constructor の仮定にせず、
  -- 入力8 normalization(§4.8)の証明義務として供給される(selected 指定の設計どおり)。

/-- 補題2.1A の比較先: 第IV部の ordered tuple cover への bridge。
simplex は次数 ≤ 2 が実 tuple データ(Index / Index² / Index³、overlap は
chart / pairCtx / tripleCtx)、次数 ≥ 3 は trivial simplex とする。 -/
def MonomorphicOrderedCover.toTupleCechCover
    (𝒰 : MonomorphicOrderedCover S) : Cohomology.CoverRelativeCechCover S
```

補題2.1A(C1)はこの bridge の上で、増加添字複体と第IV部
`CoverRelativeCechComplex` の `Z¹`/`B¹`/`H¹` 同型を証明する。
`CoverRelativeCechCover.simplex` は selected data であり全次数の実 tuple は
型の要求ではない。比較対象の `H¹`(`CoverRelativeHn 1`)は次数 ≤ 2 の成分
だけで決まるため、次数 ≥ 3 の trivial 化は補題2.1A の主張に影響しない
(実装: `Formal/AG/SemanticRepair/Saga/PartIVBridge.lean`、#3788)。

## 4. 定理1.1 の8入力の structure 設計

入力番号と structure の対応を先に固定する。

| 定理1.1 入力 | structure | 量化域 | 実装子 |
| --- | --- | --- | --- |
| (1) `M_sem` の生成データ | `AtomOccurrenceReading` + `SemanticAtomData` + `SemanticRepairPresentation` | `S_X` 全域(定義3.1) | C1 |
| (2) `Q_E` | `IntersectionCoefficientData`(generic)+ C3a realization | `Int_{≤2}(𝒰)` | C1(generic)/ C3a(`Q_E` 固定) |
| (3) 一次写像 χ | `PrimaryCoefficientCorrespondence` | `Int_{≤2}(𝒰)` | C3 |
| (4) completeness 対 | `RelationComplete` / `GeneratorComplete`(定理仮定 Prop) | `Int_{≤2}(𝒰)` の各対象 | C3 / C3a |
| (5) `P_sem` + repair atlas | `AffineSemanticRepairSystem` + `SemanticRepairAtlas` | carrier は `S_X` 全域、torsor 律は `Int_{≤2}(𝒰)` | C2 |
| (6) `P_E` + lift atlas | `AffineCoefficientLiftSystem` + `CoefficientLiftAtlas` | carrier は `S_X` 全域、作用・affine 条件は `Int_{≤2}(𝒰)` | C2 |
| (7) `β : P_sem → P_E` | `PrimaryStateCorrespondence` | `Int_{≤2}(𝒰)` | C3 |
| (8) empty-overlap normalization | `EmptyOverlapNormalization` | 省略 intersection | C1(定義)/ 各子(消費) |

### 4.1 入力1: At(V) occurrence と semantic repair presentation(定義3.1)

本文の `π_V : Λ(V) → At(V)` は context-local な Atom occurrence への projection である。
`ContextCategoryObject` は `ArchCtx` の素朴な wrapper なので、occurrence は
site 層のデータから直接定義できる:

```lean
/-- II 由来の At(V): V の support 読みが読む Atom occurrence。 -/
def AtomOccurrence {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (V : S.category) : Type u :=
  {sa : V.ctx.Support × U.Atom // V.ctx.minimal.supportReads sa.1 sa.2}
```

occurrence の restriction は選択データである。site 層の `ContextMorphism` は
support map を source → target 方向にしか持たないため、At(V) → At(V') の
restriction(第II部が概念として供給する occurrence 読みの引き戻し)は
selected structure として受ける:

```lean
/-- II 由来の At(V) presheaf 読み。occurrence restriction とその法則。 -/
structure AtomOccurrenceReading {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) : Type u where
  occRestrict : ∀ {V' V : S.category}, (V' ⟶ V) ->
      AtomOccurrence S V -> AtomOccurrence S V'
  occRestrict_id : ∀ (V : S.category) (o : AtomOccurrence S V),
      occRestrict (𝟙 V) o = o
  occRestrict_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V)
        (o : AtomOccurrence S V),
        occRestrict (f ≫ g) o = occRestrict f (occRestrict g o)
  occRestrict_atom : ∀ {V' V : S.category} (f : V' ⟶ V) (o : AtomOccurrence S V),
      (occRestrict f o).1.2 = o.1.2          -- 台 Atom は restriction で不変
```

台 Atom の object family membership は `supportReads_objectFamily` の定理であり、
field にしない。

semantic atom 側は primitive data と relation 層に分けて固定する
(relation 層の型が primitive 層から生成される `SupportedWord` を参照するため)。

```lean
/-- X.定義3.1 前半: semantic atom / restriction / projection / support。 -/
structure SemanticAtomData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (R : AtomOccurrenceReading S) : Type (max u (v + 1)) where
  SemanticAtom : S.category -> Type v                          -- Λ(V)
  restrictAtom : ∀ {V' V : S.category}, (V' ⟶ V) ->
      SemanticAtom V -> SemanticAtom V'
  restrictAtom_id : ∀ (V : S.category) (l : SemanticAtom V),
      restrictAtom (𝟙 V) l = l
  restrictAtom_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (l : SemanticAtom V),
        restrictAtom (f ≫ g) l = restrictAtom f (restrictAtom g l)
  projection : ∀ V : S.category, SemanticAtom V -> AtomOccurrence S V   -- π_V
  projection_natural : ∀ {V' V : S.category} (f : V' ⟶ V) (l : SemanticAtom V),
      projection V' (restrictAtom f l) = R.occRestrict f (projection V l)
  supported : ∀ V : S.category, SemanticAtom V -> Prop                  -- S(V) ⊆ Λ(V)
  supported_restrict : ∀ {V' V : S.category} (f : V' ⟶ V) {l : SemanticAtom V},
      supported V l -> supported V' (restrictAtom f l)
```

primitive 層から C1 が生成する対象(いずれも `D : SemanticAtomData S R` に相対):

```lean
abbrev SupportedAtom (D : SemanticAtomData S R) (V : S.category) : Type v :=
  {l : D.SemanticAtom V // D.supported V l}
abbrev SupportedWord (D : SemanticAtomData S R) (V : S.category) : Type v :=
  SupportedAtom D V →₀ ℤ                                        -- F_sem(V)(定義3.2)
def wordRestrict (D : SemanticAtomData S R) {V' V : S.category} (f : V' ⟶ V) :
    SupportedWord D V →+ SupportedWord D V'                     -- Finsupp.mapDomain
```

relation 層はこの生成対象の上で閉じる:

```lean
/-- X.定義3.1 後半 + 定義3.2: local repair relation 込みの presentation。 -/
structure SemanticRepairPresentation {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) (R : AtomOccurrenceReading S) : Type (max u (v + 1)) where
  atomData : SemanticAtomData S R
  rel : ∀ V : S.category, Set (SupportedWord atomData V)        -- Rel_rep(V)
  rel_restrict : ∀ {V' V : S.category} (f : V' ⟶ V),
      (wordRestrict atomData f) '' rel V ⊆
        ↑(AddSubgroup.closure (rel V'))                          -- res_f(Rel(V)) ⊆ ⟨Rel(V')⟩
```

C1 が生成する後続対象:

```lean
def relSpan (P : SemanticRepairPresentation S R) (V : S.category) :
    AddSubgroup (SupportedWord P.atomData V) :=
  AddSubgroup.closure (P.rel V)                                  -- R_rep(V)
def MSem (P : SemanticRepairPresentation S R) (V : S.category) : Type v :=
  SupportedWord P.atomData V ⧸ relSpan P V                       -- M_sem(V)(定義3.2)
```

命題3.3(presheaf 性)と定義3.4(`C_sem`)は C1 の proved / generated 成果である。
`C_sem` の定義は `Q_E`・幾何側複体・comparison map を参照しない(C1 受け入れ要件1)。

### 4.2 入力2: 係数 target(定義6.1 の座)

comparison core(§6–§7)の係数は intersection diagram 上でだけ量化する
(本文定義6.1「`Q` を intersection diagram 上の可換群値 presheaf とする」)。

```lean
/-- Int_{≤2}(𝒰) 上の可換群値係数データ。restriction は生成 face に沿ってだけ持つ。 -/
structure IntersectionCoefficientData {S : Site.AATSite A}
    (𝒰 : MonomorphicOrderedCover S) : Type (max u (w + 1)) where
  carrier : IntersectionIndex 𝒰 -> Type w
  addCommGroup : ∀ σ, AddCommGroup (carrier σ)
  restrict : ∀ {σ τ : IntersectionIndex 𝒰}, Face 𝒰 σ τ -> carrier τ →+ carrier σ
  restrict_coh :
      ∀ {σ τ₁ τ₂ ρ : IntersectionIndex 𝒰}
        (f₁ : Face 𝒰 σ τ₁) (g₁ : Face 𝒰 τ₁ ρ)
        (f₂ : Face 𝒰 σ τ₂) (g₂ : Face 𝒰 τ₂ ρ) (x : carrier ρ),
        restrict f₁ (restrict g₁ x) = restrict f₂ (restrict g₂ x)
```

`restrict_coh` は triple から chart への2経路の一致(presheaf functoriality の
Int_{≤2} での実体)であり、補題2.2(`δ¹δ⁰ = 0`)の証明が使う。

site 全域の presheaf(`M_sem` や `Q_E`)からの制限は C1 / C3a の generated 構成:

```lean
/-- site 全域 presheaf の Int_{≤2}(𝒰) への制限(M_sem 用は C1、Q_E 用は C3a)。 -/
def MSem.onIntersections (P : SemanticRepairPresentation S R)
    (𝒰 : MonomorphicOrderedCover S) : IntersectionCoefficientData 𝒰

/-- X.定義5.1: E から生成される Q_E = O_E / I_Ob^E の Int_{≤2}(𝒰) 読み。 -/
def equationCoefficient (S : Site.AATSite A) (𝒰 : MonomorphicOrderedCover S) :
    IntersectionCoefficientData 𝒰
  -- carrier σ := S.equationSystem.ObstructionQuotient σ.ctx
  -- restrict f := (S.equationSystem.obstructionQuotientRestrict (Face.hom f)).toAddMonoidHom
```

`ObstructionQuotient` / `obstructionQuotientRestrict`
(`Formal/AG/LawAlgebra/LawEquation.lean:108,114`)は既存 declaration であり、
#3734 の移行を待たずに使える(#3757 備考の「既存 equation-system API で閉じる」)。

### 4.3 入力3: primary coefficient correspondence(定義6.1)

```lean
/-- X.定義6.1: supported semantic atom を係数へ送る restriction-natural な一次写像。
量化域は Int_{≤2}(𝒰) の対象と生成 face。 -/
structure PrimaryCoefficientCorrespondence {S : Site.AATSite A}
    {𝒰 : MonomorphicOrderedCover S} (P : SemanticRepairPresentation S R)
    (Q : IntersectionCoefficientData 𝒰) : Type (max u v w) where
  chi : ∀ σ : IntersectionIndex 𝒰, SupportedAtom P.atomData σ.ctx -> Q.carrier σ
  chi_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : SupportedAtom P.atomData τ.ctx),
      Q.restrict f (chi τ l) =
        chi σ ⟨P.atomData.restrictAtom (Face.hom f) l.1,
               P.atomData.supported_restrict (Face.hom f) l.2⟩
```

free abelian group 上への延長
`chiHom σ : SupportedWord P.atomData σ.ctx →+ Q.carrier σ`(`Finsupp` の普遍性)は
C3 の generated 成果である。

### 4.4 入力4: completeness 対(定義6.2 の第2・第3条件)

```lean
def RelationSound (χ : PrimaryCoefficientCorrespondence P Q)
    (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ x ∈ relSpan P σ.ctx, chiHom χ σ x = 0
def RelationComplete (χ : PrimaryCoefficientCorrespondence P Q)
    (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ x : SupportedWord P.atomData σ.ctx, chiHom χ σ x = 0 -> x ∈ relSpan P σ.ctx
def GeneratorComplete (χ : PrimaryCoefficientCorrespondence P Q)
    (σ : IntersectionIndex 𝒰) : Prop :=
  ∀ q : Q.carrier σ, ∃ x : SupportedWord P.atomData σ.ctx, chiHom χ σ x = q
```

これらは定理6.3・系6.7 が `∀ σ : IntersectionIndex 𝒰` の形で仮定として受け取る
検証可能条件であり、structure の常設 field にしない(本文 §1「これらは cover
intersection ごとに確認する」)。定義6.2 第1条件(repair-relation soundness)の
受け方は route で分ける: generic な定理6.3(`SagaPresentationCore`。入力5–7 を
含まない)は本文定義6.2 どおり `RelationSound` を含む3条件を明示仮定として受ける。
equation realization route(系6.7・定理1.1)では補題6.2A(C3)が入力5–7 から
soundness を導出するため `RelationSound` を仮定に取らない(定理7.6 前文どおり)。

### 4.5 入力5: affine semantic repair system + atlas(定義4.1・4.2)

carrier・作用・restriction は `S_X` 全域で持つ(定義8.1 の sheaf condition が
site topology 上で述べられるため)。torsor 3条件は本文の帰結文
「選ばれた cover の各 intersection 上の `P_sem` は … additive torsor になる」が
量化する範囲、すなわち intersection context 上でだけ要求する。
補題4.3–系4.5・補題6.2A・定理8.2 の証明はこの範囲しか使わない。

```lean
/-- X.定義4.1: F_sem 作用つき semantic local repair state。
torsor 3条件は Int_{≤2}(𝒰) の context 上で要求する。 -/
structure AffineSemanticRepairSystem {S : Site.AATSite A}
    (P : SemanticRepairPresentation S R) (𝒰 : MonomorphicOrderedCover S) :
    Type (max u v (x + 1)) where
  State : S.category -> Type x                                  -- P_sem(V)
  restrictState : ∀ {V' V : S.category}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : ∀ (V : S.category) (p : State V), restrictState (𝟙 V) p = p
  restrictState_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (p : State V),
        restrictState (f ≫ g) p = restrictState f (restrictState g p)
  act : ∀ V : S.category, SupportedWord P.atomData V -> State V -> State V
  act_zero : ∀ (V : S.category) (p : State V), act V 0 p = p
  act_add : ∀ (V : S.category) (x y : SupportedWord P.atomData V) (p : State V),
      act V (x + y) p = act V x (act V y p)
  act_restrict : ∀ {V' V : S.category} (f : V' ⟶ V)
      (x : SupportedWord P.atomData V) (p : State V),
      restrictState f (act V x p) =
        act V' (wordRestrict P.atomData f x) (restrictState f p)
  relation_sound : ∀ (V : S.category), IsIntersectionCtx 𝒰 V ->
      ∀ x ∈ relSpan P V, ∀ p : State V, act V x p = p
  stabilizer_complete : ∀ (V : S.category), IsIntersectionCtx 𝒰 V ->
      ∀ (p : State V) (x : SupportedWord P.atomData V),
        act V x p = p -> x ∈ relSpan P V
  transitive : ∀ (V : S.category), IsIntersectionCtx 𝒰 V ->
      ∀ p q : State V, ∃ x : SupportedWord P.atomData V, q = act V x p

/-- X.定義4.2: selected local repair atlas。 -/
structure SemanticRepairAtlas {S : Site.AATSite A}
    {P : SemanticRepairPresentation S R} {𝒰 : MonomorphicOrderedCover S}
    (Psem : AffineSemanticRepairSystem P 𝒰) : Type (max u x) where
  localRepair : ∀ i : 𝒰.Index, Psem.State (𝒰.chart i)           -- p_i
```

- `stabilizer_complete` の非空性前提は witness `p` 自身が担う(本文の
  「`P_sem(V)` が非空で `x+p=p` なら」の忠実な読み)。
- semantic faithfulness は本文どおり定理として導出する(定義4.1 の注記)。field にしない。
- residual cochain `r_sem`(定義4.2)は atlas の差から C2 が生成する。
  `r_sem` を selected `1`-cocycle として供給しない(縮小禁止)。

### 4.6 入力6: `Q`-controlled lift system + atlas(定義5.3)

定義5.3 は `P_E` を「local lift を記録する presheaf」とし、affine 条件を
「各 intersection `V` で」要求する。さらに §1 入力8 は積から除いた empty
intersection 上の `P_E(V)` subsingleton 性を固定し、系8.3 は `P_E` を選ばれた
topology 上の sheaf として使う。したがって carrier と restriction は
`P_sem` と同形に `S_X` 全域の presheaf データとして持ち、`Q` 作用と affine 条件
(freeness / transitivity)は Int_{≤2}(𝒰) 上でだけ要求する。

```lean
/-- X.定義5.3: Q が作用する equation-lift local state。
carrier は presheaf、作用と affine 条件は Int_{≤2}(𝒰) 上。 -/
structure AffineCoefficientLiftSystem {S : Site.AATSite A}
    {𝒰 : MonomorphicOrderedCover S} (Q : IntersectionCoefficientData 𝒰) :
    Type (max u w (y + 1)) where
  State : S.category -> Type y                                  -- P_E(V)
  restrictState : ∀ {V' V : S.category}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : ∀ (V : S.category) (e : State V), restrictState (𝟙 V) e = e
  restrictState_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (e : State V),
        restrictState (f ≫ g) e = restrictState f (restrictState g e)
  act : ∀ σ : IntersectionIndex 𝒰, Q.carrier σ -> State σ.ctx -> State σ.ctx
  act_zero : ∀ (σ : IntersectionIndex 𝒰) (e : State σ.ctx), act σ 0 e = e
  act_add : ∀ (σ : IntersectionIndex 𝒰) (q q' : Q.carrier σ) (e : State σ.ctx),
      act σ (q + q') e = act σ q (act σ q' e)
  act_restrict : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (q : Q.carrier τ) (e : State τ.ctx),
      restrictState (Face.hom f) (act τ q e) =
        act σ (Q.restrict f q) (restrictState (Face.hom f) e)
  free : ∀ (σ : IntersectionIndex 𝒰) (e : State σ.ctx) (q : Q.carrier σ),
      act σ q e = e -> q = 0
  transitive : ∀ (σ : IntersectionIndex 𝒰) (e e' : State σ.ctx),
      ∃ q : Q.carrier σ, e' = act σ q e

/-- X.定義5.3: selected local equation-lift atlas。 -/
structure CoefficientLiftAtlas {S : Site.AATSite A}
    {𝒰 : MonomorphicOrderedCover S} {Q : IntersectionCoefficientData 𝒰}
    (PQ : AffineCoefficientLiftSystem Q) : Type (max u y) where
  localLift : ∀ i : 𝒰.Index, PQ.State (𝒰.chart i)               -- e_i
```

`r_E` は atlas の差から C2 が生成する(補題5.4 は C2 の proved 成果)。
系8.3 が追加で受け取るのは `P_E` の sheaf condition と exactness / `β` の
site 全域拡張のみである(§4.9)。

### 4.7 入力7: primary state correspondence(定義6.1B)

```lean
/-- X.定義6.1B: restriction-natural かつ generator-equivariant な β(Int_{≤2}(𝒰) 上)。 -/
structure PrimaryStateCorrespondence {S : Site.AATSite A}
    {𝒰 : MonomorphicOrderedCover S} {P : SemanticRepairPresentation S R}
    {Q : IntersectionCoefficientData 𝒰}
    (χ : PrimaryCoefficientCorrespondence P Q)
    (Psem : AffineSemanticRepairSystem P 𝒰)
    (PQ : AffineCoefficientLiftSystem Q) : Type (max u v w x y) where
  beta : ∀ σ : IntersectionIndex 𝒰, Psem.State σ.ctx -> PQ.State σ.ctx   -- β_V
  beta_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (p : Psem.State τ.ctx),
      PQ.restrictState (Face.hom f) (beta τ p) =
        beta σ (Psem.restrictState (Face.hom f) p)
  beta_equivariant : ∀ (σ : IntersectionIndex 𝒰)
      (l : SupportedAtom P.atomData σ.ctx) (p : Psem.State σ.ctx),
      beta σ (Psem.act σ.ctx (Finsupp.single l 1) p) =
        PQ.act σ (χ.chi σ l) (beta σ p)
```

equivariance は generator 水準のみ入力とする(有限和・additive inverse への延長は
作用則から従う: 本文定義6.1B)。`β` の逆写像・全単射性は field にしない(系6.5 の結論)。

### 4.8 入力8: empty-overlap normalization

```lean
/-- X.§1 入力8: 積から除いた empty intersection 上の値の固定。 -/
structure EmptyOverlapNormalization {S : Site.AATSite A}
    {𝒰 : MonomorphicOrderedCover S} (P : SemanticRepairPresentation S R)
    (Q : IntersectionCoefficientData 𝒰)
    (Psem : AffineSemanticRepairSystem P 𝒰)
    (PQ : AffineCoefficientLiftSystem Q) : Prop where
  msem_pair_trivial : ∀ i j, 𝒰.omittedPair i j ->
      ∀ x : MSem P (𝒰.pairCtx i j), x = 0
  msem_triple_trivial : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ x : MSem P (𝒰.tripleCtx i j k), x = 0
  qE_pair_trivial : ∀ i j, 𝒰.omittedPair i j ->
      ∀ x : S.equationSystem.ObstructionQuotient (𝒰.pairCtx i j), x = 0
  qE_triple_trivial : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ x : S.equationSystem.ObstructionQuotient (𝒰.tripleCtx i j k), x = 0
  psem_pair_subsingleton : ∀ i j, 𝒰.omittedPair i j ->
      Subsingleton (Psem.State (𝒰.pairCtx i j))
  psem_triple_subsingleton : ∀ i j k, 𝒰.omittedTriple i j k ->
      Subsingleton (Psem.State (𝒰.tripleCtx i j k))
  pE_pair_subsingleton : ∀ i j, 𝒰.omittedPair i j ->
      Subsingleton (PQ.State (𝒰.pairCtx i j))
  pE_triple_subsingleton : ∀ i j k, 𝒰.omittedTriple i j k ->
      Subsingleton (PQ.State (𝒰.tripleCtx i j k))
```

- 入力8 の4条件(`M_sem` / `Q_E` の零化、`P_sem` / `P_E` の subsingleton 性)は
  すべて R0 で型固定される。`Q` の Int_{≤2} データは省略 intersection を対象に
  持たないため、`Q_E` の normalization は site 全域実体(`ObstructionQuotient`)に
  対して述べる。`P_sem` / `P_E` は carrier が `S_X` 全域にあるため
  省略 intersection 上で直接述べられる(§4.5、§4.6)。
- normalization は selected datum として structure に現れ、導出や省略で置換しない
  (C1 受け入れ要件4)。消費箇所は補題2.1A(C1)と定理8.2 の matching family 化(C5)。

### 4.9 3層の bundle: generic core / equation packet / 定理1.1 signature

レビュー指摘どおり、generic な定理6.3 用の bundle と、`Q_E` へ固定した
系6.7 / 定理7.6 用の packet、定理1.1 の最終 signature を分けて固定する。

```lean
/-- 定理6.3(Coefficient Presentation Theorem)用の generic bundle。
completeness 対は bundle に入れず定理仮定として受け取る。 -/
structure SagaPresentationCore (S : Site.AATSite A) : Type _ where
  occurrenceReading : AtomOccurrenceReading S
  cover : MonomorphicOrderedCover S
  presentation : SemanticRepairPresentation S occurrenceReading      -- 入力1
  coefficient : IntersectionCoefficientData cover                    -- 入力2(generic)
  correspondence :
    PrimaryCoefficientCorrespondence presentation coefficient        -- 入力3

/-- X.命題6.1A: λ ↦ (i_λ, A_λ) の selected 対応(π(λ) は presentation の projection)。 -/
structure EquationSemanticRealization {S : Site.AATSite A}
    (P : SemanticRepairPresentation S R) (𝒰 : MonomorphicOrderedCover S) :
    Type (max (u + 1) v) where
  -- ArchitectureObject U : Type (u + 1) を field 値に持つため universe は u+1
  lawIndex : ∀ σ : IntersectionIndex 𝒰,
      SupportedAtom P.atomData σ.ctx -> S.equationSystem.Index       -- i_λ
  lawIndex_required : ∀ σ l, S.equationSystem.Required (lawIndex σ l)
  lawIndex_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : SupportedAtom P.atomData τ.ctx),
      lawIndex σ ⟨P.atomData.restrictAtom (Face.hom f) l.1,
                  P.atomData.supported_restrict (Face.hom f) l.2⟩ = lawIndex τ l
  archReading : ∀ σ : IntersectionIndex 𝒰,
      SupportedAtom P.atomData σ.ctx -> ArchitectureObject U         -- A_λ
  archReading_natural : ∀ {σ τ : IntersectionIndex 𝒰} (f : Face 𝒰 σ τ)
      (l : SupportedAtom P.atomData τ.ctx),
      archReading σ ⟨P.atomData.restrictAtom (Face.hom f) l.1,
                     P.atomData.supported_restrict (Face.hom f) l.2⟩ = archReading τ l

/-- 系6.7(Equation Coefficient Comparison)用の packet。
coefficient と correspondence は選択せず、E と realization から生成する。 -/
structure SagaEquationPacket (S : Site.AATSite A) : Type _ where
  occurrenceReading : AtomOccurrenceReading S
  cover : MonomorphicOrderedCover S
  presentation : SemanticRepairPresentation S occurrenceReading      -- 入力1
  realization : EquationSemanticRealization presentation cover       -- 入力3の生成源
  -- 生成: coefficient := equationCoefficient S cover                -- 入力2(Q_E 固定)
  -- 生成: correspondence := χ^E(realization から。命題6.1A、C3a)
  repairSystem : AffineSemanticRepairSystem presentation cover       -- 入力5a
  repairAtlas : SemanticRepairAtlas repairSystem                     -- 入力5b
  liftSystem : AffineCoefficientLiftSystem (equationCoefficient S cover)  -- 入力6a
  liftAtlas : CoefficientLiftAtlas liftSystem                        -- 入力6b
  stateCorrespondence :
    PrimaryStateCorrespondence (chiE realization) repairSystem liftSystem  -- 入力7
  normalization :
    EmptyOverlapNormalization presentation
      (equationCoefficient S cover) repairSystem liftSystem          -- 入力8
```

`χ^E σ l := [ε_{σ,A_λ,i_λ,π(λ)}]` は `equationResidual` + `Ideal.Quotient.mk` から
C3a が構成し(`chiE`)、naturality は `equationResidual_restrict` +
`obstructionQuotientRestrict_mk` で証明する。residual の Atom 引数は
`(P.atomData.projection σ.ctx l.1).1.2`(occurrence の台 Atom)である。

定理1.1 の名を持つ最終 statement(C4/C5)の signature:

```lean
theorem sagaCentralTheorem {S : Site.AATSite A}
    (inputs : SagaEquationPacket S)
    [Fintype inputs.cover.Index]                       -- 本文 §1 の有限添字集合
    (relComplete : ∀ σ, RelationComplete (chiE inputs.realization) σ)   -- 入力4a
    (genComplete : ∀ σ, GeneratorComplete (chiE inputs.realization) σ)  -- 入力4b
    : SagaCentralTheoremConclusions inputs             -- Φ同型・κ可換・H¹同型・residual対応
```

定理8.2・系8.3 は上記に加えて `TopologicalMonomorphicCover` の `mem_topology`、
`P_sem` の topology 上の sheaf condition(定義8.1。既存 `Site.AATSheafCondition`
API に接続)、系8.3 では exactness / `β` の site 全域拡張を追加仮定として受け取る
(本文 系8.3「SAGA presentation exactness と primary state correspondence が
`S_X` 上で成立し」)。C5 が固定する。

## 5. field にしないもの(縮小禁止リスト対応)

次は定理の結論または generated 対象であり、いかなる structure の field にもしない。

- `Φ` とその逆写像、`Φ` の同型性(定理6.3 の結論)
- `κ^n` と微分可換性(定義7.1 は generated、定理7.2 は proved)
- `r_sem` / `r_E` の cocycle 性(補題4.3・補題5.4 の結論)、`r_sem`・`r_E` 自体
  (atlas の差から generated)
- `H¹` 同型・residual class 対応・Nonempty 同値(定理7.4–7.6・定理8.2 の結論)
- repair-relation soundness(structure field にしない。generic 定理6.3 では
  明示仮定 `RelationSound`、equation route では補題6.2A が入力5–7 から導出。§4.4)
- semantic faithfulness(定義4.1 の注記どおり定理)
- `β` の全単射性(系6.5 の結論)
- per-cover amalgamation map(定義8.1「別データとして置かない」。C5 は
  `S_X` topology 上の sheaf condition から `𝒰` に対する条件を導出する)
- `r_sem` を幾何側 residual の逆像として定義しない(縮小禁止リスト)
- Atom occurrence の object family membership(`supportReads_objectFamily` の定理)

本文が量化する一般対象に対して入力を強めない。具体的には:

- `Q` / `χ` / `P_E` / `β` は Int_{≤2}(𝒰) 上でだけ量化する(§4.2–§4.7)。
  site 全域の量化は本文にない premise の追加であり、採らない。
- `Index` の有限性は comparison core(定理6.3–8.2)の入力にせず、
  定理1.1 の名を持つ最終 statement だけが `[Fintype]` で受ける(§3.2、§4.9)。

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
| `SemanticRepairCoverH1BoundaryRelationAbelianData`, `SemanticRepairCoverH1FaithfulnessData`, `GlobalRepairCoherent`, `zero1_is_boundary`, `globalRepairCoherent_of_boundary`, `SemanticRepairCoverH1AdditiveFaithfulnessData`, `toFaithfulnessData`(3箇所), `toAdditiveCechH1Data`(2箇所), `globalRepairCoherent_of_additiveH1Zero`(2箇所), `toFiniteGluingComplex`, `semanticFaithfulnessHypotheses`, `toFaithfulnessData_globalRepairCoherent_iff`, `SemanticRepairCoverH1BoundaryRelationAdditiveData`, `toAdditiveFaithfulnessData` | 置換候補(C2 定義4.1 の relation_sound / stabilizer_complete / transitive が supplied faithfulness 系を置換) |
| `TrueSheafConditionCertificate`, `coverSheafConditionFor_of_trueSheafCertificate`, `coverDescent_of_trueSheafCertificate`, `trueSheafH1SemanticRepairGluing_boundaryRelationAdditive_package` | 置換候補(certificate とその直接 consumer を同区分で扱う。`…_package` は certificate を仮定に取り上記2定理を証明で使用: `AdditiveH1.lean:1865-1896`。C5 定義8.1 は per-cover certificate を置かず topology-wide sheaf condition から導出) |
| `AdditiveRepairSolution`, `additiveRepairGaugeSubgroup`, `AdditiveRepairGauge`, `additiveRepairGaugeAddCommGroup`, `AdditiveRepairPrimitiveTranslation`, `additiveRepairPrimitiveTranslation`, `additiveRepairGaugeBetween`, `additiveRepairGaugeAction`, `additiveRepairGaugeAddAction`, `additiveRepairGaugeAction_zero/_add`, `additiveRepairGaugeBetween_action`, `additiveRepairGaugeAction_free`, `AdditiveRepairGaugeActsSimplyTransitively`, `additiveRepairGaugeActsSimplyTransitively`, `additiveRepairSolution_of_h1Zero`, `additiveRepairSolution_nonempty_iff_h1Zero`, `AdditiveTorsorTrivial`, `additiveTorsorTrivial_of_additiveH1Zero` | reuse(C2 torsor・C5 effectivity の proof pattern)→ C8 で退役裁定 |
| `SelectedHigherCoherenceDefect`, `SelectedHigherCoherenceTrivialization`, `HigherCoherenceVanishes`, `selectedHigherCoherenceTrivialization_of_additive`, `selectedHigherCoherence_facewise`, `higherCoherenceVanishes_of_additive`, `additiveRepairCoverStackBase`, `AdditiveFiberTranslation`, `additiveFiberTranslation`, `additiveFiberTranslation_unique`, `additiveRepairCoverTranslationPresheaf`, `residualTransition_eq_localDifference`, `selectedRepairLocalObjects`, `selectedRepairDescentDatum`, `selectedRepairEffectiveDescent_of_h1Zero`, `StackEffectivelyVanishes`, `stackEffectivelyVanishes_of_additive`, `selectedHigherCoherenceAndEffectiveDescent_of_additive`, `globalRepairCoherent_iff_additiveH1Zero` | 維持(原則8.4 の higher / stack 面。新 route のスコープ外。`globalRepairCoherent_iff_additiveH1Zero` は `TrueSheafConditionCertificate` を消費しないことを docstring と実装で確認済み) |
| `SemanticRepairAdditiveFiniteComparison`, `finiteShadow_obstructionVanishes_of_coverBoundary`, `coverBoundary_of_finiteShadow_obstructionVanishes`, `additiveH1Zero_iff_finiteShadow_obstructionVanishes`, `finiteShadowComparison_package`, `SemanticRepairCoverRefinement`, `SemanticRepairAdditiveRefinementComparison`, `refinement_boundary_pullback`, `refinement_additiveH1Zero_pullback`, `refinementPullback_package` | 維持(有限比較・refinement。C7 の比較材料) |

維持・reuse 区分の宣言群(higher / stack 面、有限比較・refinement)は、置換候補区分の
additive Čech surface(`SemanticRepairCoverCechData` / `CechZ1` / `CechB1` /
`toAdditiveCechH1Data` 等)の上に定義されている。「維持」は宣言を保持する意図を表し、
C8 が置換候補を退役させる場合は、維持宣言の新 route surface への再基底化か、
保持・退役の同時裁定を行う(片側だけの退役はしない)。

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
**維持**(no-go theorem / counterexample 資産。#3242 裁定(C8)の一次材料)。

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

- `SemanticAtomProjection`, `Support` — **reuse**(§4.1 `SemanticAtomData` の先行素材。
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
  (site 接続定理。§3.2 `mem_topology` の放電にも使える)。
- `SemanticRepairCoverRelativeCoverBridge`, `toCoverRelativeCechCover`,
  `EmptyIndexZeroSimplexIncidenceNoGo`, `no_incidence`,
  `no_constructor_from_coverBridge_without_zeroSimplexChartIncidence`,
  `chartIndexedZeroCover_constructs_zeroSimplexChartIncidence`,
  `coverNerve_typedComponent_adequacy`,
  `aatSheafCondition_coverMembership_descent_effectiveGluing` — **reuse**
  (§3.3 bridge・C5 sheaf condition 接続の素材)。

### 外部依存ファイル

- `Formal/AG/Examples/SemanticRepairPart10.lean`(4024行)/
  `SemanticRepairPart10SiteGeometry.lean` — **凍結**(旧 route fixture)。
  C7 の circle witness(例10.2 / 付録B.9)は新規に作り、旧 fixture を流用しない。
- `Formal/AG/AxiomAudit.lean` の SemanticRepair 収載行 — 維持。C8 で新旧対応表を反映。

## 7. G-07 対応表の採用(R0-3)

#3757 本文の G-07 対応表(15 label)を R0 の固定 map として採用する。
全 label の実在と完全修飾名を検証済み。namespace root は
`ResearchLean.AG.QualitySurface` であり、以下では `RQS` と略記する
(略記は本 note の表記のみ。Lean 側の名称は完全修飾名を正とする)。

5 label(`localLiftDifferenceFor`, `localLiftDifferenceFor_cocycle`,
`connectingClass_choice_independent`, `correctedLocalLiftCochain_d_eq_zero`,
`amalgamatedCorrectedLocalLift`)は small-cover 版と large-coefficient 版の
2宣言が同名で存在する。large 版の定理群は namespace
`LawGeneratedLargeConormalDescent.LocalLiftData` 内、small 版は namespace
`LawGeneratedConormalDescent.SmallCanonicalTupleCover.LiftProblem` 内にある
(structure `LocalLiftData` 自体は namespace 外)。表の完全修飾名はこれを含む。
**C6 が蒸留する statement family は large-coefficient 版を正とする**
(`LocalLiftData` と `connectingClassFor_isZero_iff_nonempty_globalLift` は
large 版にのみ存在し、総合パッケージ定理も large 系を積む)。small 版は
proof pattern の補助参照とする。

| G-07 label | 完全修飾名(採用 statement family) | 所在 | 扱い |
| --- | --- | --- | --- |
| `PatchReadingSource` | `RQS.LawGeneratedSemanticFirstOrderRepair.PatchReadingSource` | `LawGeneratedSemanticFirstOrderRepair.lean:81` | generalize |
| `OverlapLawCombination` | `RQS.LawGeneratedSemanticFirstOrderRepair.OverlapLawCombination` | 同 `:158` | generalize |
| `evaluateCombination_mem_obstructionIdeal` | `RQS.LawGeneratedSemanticFirstOrderRepair.evaluateCombination_mem_obstructionIdeal` | 同 `:191` | reuse pattern |
| `rawQ0_pair_compatible` | `RQS.LawGeneratedSemanticFirstOrderRepair.rawQ0_pair_compatible` | 同 `:214` | specialization |
| `LocalLiftData` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData` | `LawGeneratedLargeConormalDescent.lean:101` | reuse |
| `localLiftDifferenceFor` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.localLiftDifferenceFor`(補助: `RQS.LawGeneratedConormalDescent.SmallCanonicalTupleCover.LiftProblem.localLiftDifferenceFor:352`) | 同 `:234` | reuse |
| `localLiftDifferenceFor_cocycle` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.localLiftDifferenceFor_cocycle`(補助: small 版 `:369`) | 同 `:249` | reuse |
| `connectingClass_choice_independent` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.connectingClass_choice_independent`(補助: small 版 `:447`) | 同 `:330` | reuse |
| `correctedLocalLiftCochain_d_eq_zero` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.correctedLocalLiftCochain_d_eq_zero`(補助: small 版 `:658`) | 同 `:541` | reuse |
| `amalgamatedCorrectedLocalLift` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.amalgamatedCorrectedLocalLift`(補助: small 版 `:849`) | 同 `:711` | reuse |
| `connectingClassFor_isZero_iff_nonempty_globalLift` | `RQS.LawGeneratedLargeConormalDescent.LocalLiftData.connectingClassFor_isZero_iff_nonempty_globalLift` | 同 `:779` | reuse |
| `SemanticFirstOrderRepair` | `RQS.LawGeneratedSemanticFirstOrderRepair.SemanticFirstOrderRepair` | `LawGeneratedSemanticFirstOrderRepair.lean:737` | specialization |
| `SemanticFirstOrderRepairEquiv` | `RQS.LawGeneratedSemanticFirstOrderRepair.SemanticFirstOrderRepairEquiv` | 同 `:863` | specialization |
| `connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair` | `RQS.LawGeneratedSemanticFirstOrderRepair.connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair` | 同 `:872` | specialization |
| `lawGeneratedConormalFirstOrderDescent_package` | `RQS.LawGeneratedConormalFirstOrderDescentPackage.lawGeneratedConormalFirstOrderDescent_package` | `LawGeneratedConormalFirstOrderDescentPackage.lean:239` | specialization |

import 経路も #3757 の記載どおりであることを確認した:
`LawGeneratedLargeCoefficientCech.lean` の `Formal/AG` 側 import は generic な
`Formal.AG.Cohomology.CochainComparison`(+ `Site.FinitePosetGeometry`)のみで、
`SemanticRepairCechGrounding` / `SagaComparison` / `H1Comparison` を import しない
(非循環)。

universe 接続: 大係数資産の conormal lift / state は `Type (u+1)` に実体を持つ。
§1 の universe 規約(係数 `w`・状態 `x`/`y` の分離)により、C6 は蒸留時に
`w := u + 1` 等の instantiation で受けられる。site universe への transport は不要である。

運用は #3757 記載のとおり: reuse / generalize 分は C1–C5 の構成で proof pattern
として使い、C6(#3767)で `Formal/` へ蒸留する。specialization 分は C6 が
first-order conormal instance として固定する。蒸留は本体内での再構成であり、
`ResearchLean` の import ではない(`docs/aat/guideline.md`「移植 ≠ import」)。

## 8. C1–C8 への引き渡し

| 子 | 本 note の対応節 | 実装する generated / proved 対象 |
| --- | --- | --- |
| C1 #3762 | §3, §4.1, §4.2(generic), §4.8 | `Face.hom`、増加添字三項複体、補題2.1A bridge(`ofOverlapPackage` / `toTupleCechCover`)、`SupportedWord`/`wordRestrict`/`relSpan`/`MSem`、命題3.3、定義3.4、mono 自動成立 instance |
| C2 #3763 | §4.5, §4.6 | torsor 帰結(freeness / faithfulness)、`r_sem`/`r_E` 生成、補題4.3–系4.5、補題5.4 |
| C3 #3764 | §4.3, §4.4, §4.7 | `chiHom`、補題6.2A、定理6.3(`SagaPresentationCore` + `RelationSound`/`RelationComplete`/`GeneratorComplete` の3条件仮定)、系6.4–6.5、例6.6 negative fixture |
| C3a #3771 | §4.2(realization), §4.9 | `equationCoefficient`、`EquationSemanticRealization`、`chiE`、命題6.1A、系6.7(`SagaEquationPacket`) |
| C4 #3765 | §4.9, §5 | `κ^n`、定理7.2–7.6、`sagaCentralTheorem` の比較部 |
| C5 #3766 | §3.2, §4.8, §4.9 | 定義8.1(`TopologicalMonomorphicCover` + topology-wide sheaf condition)、定理8.2、系8.3(site 全域拡張仮定込み) |
| C6 #3767 | §1(universe 規約), §7 | G-07 蒸留 + conormal specialization |
| C7 #3768 | §3.2(有限 specialization) | circle witness(例10.2 / 付録B.9)、#3718 吸収 |
| C8 #3769 | §6 | 存廃裁定の最終化、#3242 裁定、AxiomAudit / fixture / 台帳同期 |

signature の細部(implicit 引数の形、`Finsupp` の具体 API、`abbrev` / `def` の別、
universe 変数の並び)は実装子が調整してよい。ただし入力番号と structure の対応
(§4 冒頭表)、量化域(Int_{≤2} / site 全域の別)、§5 の「field にしないもの」、
§6 の凍結区分への新規依存禁止を変更する場合は、本 note を更新し子 PR で明記する。
