# ArchMap Atom-to-AAT Presentation Contract PRD

この PRD は、ArchMap v1 の target contract を定義する。

ArchMap v1 は、source code / docs / tests / traces から作る atoms と molecules を、
ArchSig が tooling contract 上の AAT-compatible presentation へ正規化できる形で保存する
atom map contract である。ArchSig はその normalized presentation を LawPolicy に相対化して読み、
bounded diagnostic conclusion を計算する。

この v1 は破壊的変更である。現行 tooling はまだ v0.3.2 であり、v0 schema の後方互換、
dual reader、legacy alias、compatibility shim を維持しない。レガシーを作らず、v1 contract へ
素直に移行する。

```text
source code / docs / tests / traces
  -> ArchMap authoring layer
     source-derived atoms と molecule membership を保存する
  -> ArchSig normalizer
     ArchMap を tooling contract 上の AAT-compatible Atom presentation へ変換する
  -> LawPolicy
     採用する law / evaluator / basis / scope / severity を選ぶ
  -> ArchSig evaluator
     obstruction / signature / distance / homotopy / review focus を計算する
```

この文書でいう minimalization は、source から書ける atoms と molecules を主役にし、
derived diagnosis を ArchSig 側の computation artifact へ移すことである。

## Core Thesis

**ArchMap は atom-to-presentation contract である。source-derived atoms と molecules を保存し、
ArchSig normalizer がそれを tooling contract 上の AAT-compatible presentation へ正規化する。**

この一文を設計の中心に置く。

- ArchMap author は source-derived atoms と molecule membership を書く。
- ArchSig normalizer は ArchMap を source 再読込なしで typed normalized model へ変換する。
- unsupported atom は validation error にし、composition / required port が成立しない molecule は
  normalization blocker として扱う。
- ArchSig evaluator は normalized model と LawPolicy だけから bounded diagnostic conclusion を出す。
- ArchSig は Lean に依存しない計算器であり、Lean を呼ばず、Lean proof object を要求しない。
- missing atom は、ArchSig evaluator が `blocked` / `unknown` / `unmeasured` として扱う。
- v0 input compatibility は維持しない。v0 artifact は migration note の対象であり、runtime contract ではない。

## Responsibility Split

| Layer | Owns | Delegates to |
| --- | --- | --- |
| ArchMap authoring layer | source-derived atoms、explicit molecule membership、source refs | AAT presentation は normalizer、diagnosis は ArchSig evaluator |
| ArchSig normalizer | ArchMap atoms から tooling contract 上の AAT-compatible Atom presentation / molecule candidate を作る | diagnosis は evaluator、policy selection は LawPolicy。Lean proof discharge はこの contract の対象外 |
| LawPolicy | repository が採用する law、evaluator、basis、scope、severity の選択 | witness / axis / missing blocker / obstruction / measurement の計算規則は evaluator registry |
| ArchSig evaluator | normalized presentation と LawPolicy から bounded diagnostic result を計算する | Lean theorem discharge はこの contract の対象外、evolution reading は FieldSig |
| FieldSig | ArchSig packet を SFT 側の evolution / governance input として読む | current structural diagnosis は ArchSig |

## Design Principles

### 1. Atom-native first

ArchMap primary schema は、code / docs / tests / traces を読んだ author が無理なく書ける形にする。
`AtomShape`、`AtomValence`、required port graph、compatible composition への変換は
ArchSig normalizer が引き受ける。

ArchMap author が書くのは、たとえば次のような atom である。

```json
{
  "id": "atom:place-order-capability",
  "kind": "capability",
  "subject": "domain.OrderService",
  "predicate": "placesOrder",
  "refs": ["src.app.place_order"]
}
```

これは source から書ける。これを tooling contract 上の AAT-compatible な `AtomKind.capability`、
`Axis.static`、shape coordinate、port surface へ落とすのは ArchSig normalizer の責務である。

### 2. Typed atoms

ArchMap primary は、機械的に検査できる typed atom として書く。
ArchSig は ArchMap の `atoms` を input records として扱う。AAT root の Atom object は
Lean / AAT 側の対象である。

- `kind` は `AtomPredicate` constructor に対応する registry enum であり、unknown string は validation error。
- `predicate` と constructor-specific payload は controlled vocabulary である。
- constructor-specific ref fields と `refs` は source table の id に解決される。
- `label` や reviewer memo は表示 / authoring memo である。

ArchMap primary に現れる文字列は、意味そのものではなく、次のどれかでなければならない。

- schema / registry が定義する enum token。
- `sources` に解決される source id。
- registry が定義する predicate id。
- author が同じ artifact 内で定義した atom / molecule id。

Predicate registry は atom constructor ごとに required field shape を公開する。
たとえば `capability` は `subject` / `predicate`、`effect` は `diagram` / `effect`、
`runtime` は `edge` / `interaction` を要求する。任意の prose payload や
未解決 namespace は validation error である。

JSON は保存形式にすぎない。ArchSig 内部では typed normalized model に変換してから evaluator を走らせる。

### 3. Normalization carries AAT compatibility

AAT compatibility は、ArchMap primary の atoms を deterministic normalizer が
tooling contract 上の AAT-compatible presentation へ写せることとして扱う。

```text
ArchMap typed atom records
  -> deterministic normalizer
  -> tooling contract 上の AAT-compatible Atom presentation
```

Normalizer は、valid ArchMap の atom を `AtomKind`、`Axis`、typed predicate、shape coordinate、
valence template、molecule compatibility check へ写す。

この mapping は、valid ArchMap contract に対して決定論的かつ total である。つまり、
validation を通過した atom は必ず normalized atom presentation を持つ。registry に mapping がない
atom kind / predicate / shape は valid ArchMap ではなく、analysis 前の validation error である。

`AAT-compatible` は Lean runtime dependency を意味しない。ArchSig は Lean を import / call せず、
Lean theorem を discharge せず、Lean proof object を生成しない。ここでいう compatibility は、
ArchSig の registry contract が AAT の current atom vocabulary / predicate grammar と同じ責務境界を
保つ、という tooling contract である。

### 4. Explicit molecule membership, normalized generated evidence

Molecule membership は、ArchMap author が「同じ局所 configuration に属する atom 群」を
明示する input である。

ArchMap author が AAT の `GeneratedMolecule` 証拠を手で書く必要はない。Normalizer が、
explicit molecule membership と atom facts から、AAT-compatible generated molecule candidate
として読めるかを判定する。

```text
author input:
  molecule membership

normalizer output:
  generated molecule candidate
  required port / composition evidence status
  normalized / blockedForNormalization status
```

`measuredPass`、`measuredViolation`、`blocked`、`unknown`、`unmeasured` は evaluator result の
status である。

### 5. LawPolicy selects, evaluator computes

LawPolicy は、repository が採用する law と、それを読む versioned evaluator を選ぶ。

witness predicate、axis valuation、missing blocker rule、obstruction definition は、
evaluator registry の実装と manifest が所有する。

Measurement、aggregation、threshold、distance contribution、review focus は evaluator registry が
所有する。LawPolicy はそれらを DSL や score formula として持たない。

### 6. Positive bounded conclusions

ArchSig は、与えられた `ArchMap + LawPolicy + evidence contract` から語れることだけを語る。
ここでいう evidence contract は ArchMap schema と evaluator registry が定義する evidence boundary であり、
追加の side input ではない。
語れる範囲では `SAFE_WITHIN_POLICY`、`NO_SELECTED_OBSTRUCTION`、
`ACCEPTABLE_UNDER_EVIDENCE_CONTRACT` のような肯定的な bounded conclusion を出す。
語るための atom / molecule が足りない箇所は `blocked` / `unknown` / `unmeasured` として扱い、
measured zero へ落とさない。

## Artifact Contract

### ArchMap Primary Artifact

ArchMap primary artifact は、source-derived atoms と molecule membership を保存する。

```json
{
  "schema": "archmap/v1",
  "id": "practical-rust-service",
  "sources": {
    "src.app": { "kind": "file", "path": "sample/src/app.rs" },
    "src.app.place_order": {
      "kind": "symbol",
      "source": "src.app",
      "symbol": "place_order",
      "line": 23
    },
    "domain.OrderService": {
      "kind": "symbol",
      "source": "src.app",
      "symbol": "OrderService"
    },
    "domain.Order": {
      "kind": "symbol",
      "source": "src.app",
      "symbol": "Order"
    },
    "domain.InventoryService": {
      "kind": "symbol",
      "source": "src.app",
      "symbol": "InventoryService"
    },
    "domain.InventoryReservation": {
      "kind": "symbol",
      "source": "src.app",
      "symbol": "InventoryReservation"
    }
  },
  "atoms": [
    {
      "id": "atom:place-order-capability",
      "kind": "capability",
      "subject": "domain.OrderService",
      "predicate": "placesOrder",
      "refs": ["src.app.place_order"],
      "label": "OrderService places an order"
    },
    {
      "id": "atom:inventory-check",
      "kind": "relation",
      "subject": "domain.OrderService",
      "predicate": "checksInventoryWith",
      "object": "domain.InventoryService",
      "refs": ["src.app.place_order"],
      "label": "OrderService checks inventory through InventoryService"
    },
    {
      "id": "atom:reserve-effect",
      "kind": "effect",
      "diagram": "src.app.place_order",
      "effect": "createsInventoryReservation",
      "refs": ["src.app.place_order"],
      "label": "InventoryService creates an inventory reservation"
    }
  ],
  "molecules": [
    {
      "id": "mol:place-order-flow",
      "atoms": [
        "atom:place-order-capability",
        "atom:inventory-check",
        "atom:reserve-effect"
      ],
      "refs": ["src.app.place_order"],
      "label": "place_order local flow"
    }
  ]
}
```

ArchMap primary に置くもの:

- `sources`: 読んだ source の台帳。
- `atoms`: source-derived atoms。
- `molecules`: author が明示した局所 configuration membership。
- `refs`: source 台帳への参照。
- `label`: 人間向け表示。evaluator は読まない。

ArchMap primary に置かないもの:

- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`
- `nonConclusions`
- obstruction / signature / distance / holonomy / risk / review focus
- AtomShape / AtomValence / compatible composition の完全手書き

### Unknown / Missing Atom

ArchSig core input は `ArchMap + LawPolicy` に固定する。

ArchMap primary の `sources` は読んだ source の台帳である。source inventory audit は
ArchMap authoring run metadata、review note、CI report、または別 tooling が扱う。

Evaluator が要求する atom / molecule / source ref が ArchMap に存在しない場合、ArchSig は
その evaluator result を `unknown` / `unmeasured` / `blocked` にする。missing を measured zero と
して扱わない。

### Atom Vocabulary

Atom vocabulary は、Lean 側の current `AtomPredicate` grammar に対応する
ArchMap authoring constructor vocabulary である。
ArchMap authoring では書きやすい短い constructor 名を使い、normalizer が Lean-facing
`AtomPredicate` constructor へ total に写す。

| ArchMap atom constructor | Required shape | Normalized predicate | AtomKind | Axis |
| --- | --- | --- | --- | --- |
| `component` | `subject` | `AtomPredicate.component(subject)` | `existence` | `static` |
| `relation` | `edge` または `subject`, `object`, `predicate` | `AtomPredicate.relation(edge)` | `relation` | `static` |
| `capability` | `subject`, `predicate` | `AtomPredicate.capability(subject, predicate)` | `capability` | `static` |
| `dataState` | `diagram`, `state` | `AtomPredicate.dataState(diagram, state)` | `dataState` | `dataflow` |
| `effect` | `diagram`, `effect` | `AtomPredicate.effect(diagram, effect)` | `effect` | `semantic` |
| `authority` | `subject`, `authority` | `AtomPredicate.boundaryAuthority(subject, authority)` | `boundaryAuthority` | `boundary` |
| `contract` | `diagram`, `contract` | `AtomPredicate.contractSpecification(diagram, contract)` | `contractSpecification` | `specification` |
| `semantic` | `diagram`, `meaning` | `AtomPredicate.semanticInterpretation(diagram, meaning)` | `semanticInterpretation` | `semantic` |
| `runtime` | `edge`, `interaction` | `AtomPredicate.runtimeInteraction(edge, interaction)` | `runtimeInteraction` | `runtime` |

`AtomPredicate.custom` は default ArchMap v1 vocabulary には含めない。使う場合は、registry extension が
`AtomKind`、`Axis`、required shape、normalizer mapping、negative fixture を明示する。

この表は、ArchMap atom を current Lean-facing predicate grammar へ total に変換するための
normalizer contract である。

ArchSig は missing blocker を、evaluator requirement、LawPolicy scope、
atoms / molecules の照合からだけ出す。

### Normalized ArchMap Artifact

Normalized ArchMap は、ArchSig normalizer が生成する computation artifact である。

Normalized artifact は少なくとも次を持つ。

- source atom id
- normalized atom id
- `AtomKind`
- `Axis`
- typed predicate constructor / normalized predicate name
- subject / object / payload bindings
- shape coordinate status
- valence template id
- molecule membership
- generated molecule candidate status
- normalization status: `normalized` / `blockedForNormalization`
- normalization blocker reason

Normalizer は source repository を再読込しない。ArchMap primary と evaluator registry だけを読む。

## LawPolicy Contract

LawPolicy は、対象 repository / organization / review context が採用する architecture policy と、
それを読む ArchSig evaluator を選ぶ artifact である。

```json
{
  "schema": "law-policy/v1",
  "id": "practical-rust-service-policy",
  "policies": [
    {
      "pack": "solid@1",
      "basis": ["docs.architecture.design_principles"],
      "scope": ["src/**"],
      "severity": "advisory"
    },
    {
      "law": "domain.no-direct-infra-dependency",
      "evaluator": "domain.no-direct-infra-dependency@1",
      "basis": ["docs.architecture.layering"],
      "scope": ["src/domain/**"],
      "severity": "review-blocking"
    }
  ]
}
```

LawPolicy に置くもの:

- policy pack id / version
- law id
- evaluator id / version
- law basis refs
- source scope
- severity

LawPolicy に置かないもの:

- generated witness predicate
- generated signature axis
- generated missing blocker requirement
- exactness assumption DSL
- obstruction circuit definition
- molecule pattern DSL
- measurement profile / calibration profile
- score expression / formula
- evaluator-local witness generation rule

Unknown pack、unsupported pack version、unknown evaluator、unsupported evaluator version、unresolved basis、
code-shape-only basis は analysis 前の hard validation error である。

Evaluator id / version が、measurement、aggregation、threshold、distance contribution、review focus の
計算 contract を決める。LawPolicy は evaluator を選ぶだけで、計算 contract を上書きしない。

### Policy Packs and Expressiveness

LawPolicy は単一 law だけでなく、registry-defined policy pack を選べる。Policy pack は
複数 law entry の shorthand であり、LawPolicy 内で展開規則や criteria を定義しない。

たとえば SOLID は次のように表現できる。

```json
{
  "pack": "solid@1",
  "basis": ["docs.architecture.design_principles"],
  "scope": ["src/**"],
  "severity": "advisory"
}
```

ArchSig は registry から `solid@1` を次のような law family に展開する。

| Law | Evaluator |
| --- | --- |
| `solid.single-responsibility` | `solid.single-responsibility@1` |
| `solid.open-closed` | `solid.open-closed@1` |
| `solid.liskov-substitution` | `solid.liskov-substitution@1` |
| `solid.interface-segregation` | `solid.interface-segregation@1` |
| `solid.dependency-inversion` | `solid.dependency-inversion@1` |

Pack entry の `basis` / `scope` / `severity` は展開された各 law entry に引き継がれる。
特定 law だけ severity や scope を変える場合は、pack ではなく明示的な law entry を書く。

SOLID のような抽象 principle は、ArchSig が global design quality を証明する対象ではない。
各 evaluator は、ArchMap の atoms / molecules から読める support に限って
`measuredPass` / `measuredViolation` / `blocked` / `unknown` / `unmeasured` を返す。

### Law Evaluation Procedure

Law は LawPolicy の中で計算されない。LawPolicy の各 `policies[]` entry が evaluator id / version を
選び、ArchSig が evaluator registry の contract に従って計算する。

各 evaluator は registry manifest で次を公開する。

- evaluator id / version
- 対象 law id
- required atom constructors / predicates
- required molecule membership / composition condition
- scope filtering rule
- missing atom / missing molecule blocker rule
- measured pass / measured violation criteria
- typed result schema
- detail refs / basis refs の出力位置
- negative fixtures

ArchSig は各 policy entry について次の順に実行する。

```text
1. pack entry を registry-defined law entries へ展開する。
2. law / evaluator / basis / scope / severity を validate する。
3. normalized ArchMap から scope 内の atoms / molecules を選ぶ。
4. evaluator manifest の required atom / molecule shape を照合する。
5. required support が足りない場合は `unknown` / `unmeasured` / `blocked` を出す。
6. required support がそろう場合だけ law-specific evaluator を実行する。
7. evaluator result を `measuredPass` / `measuredViolation` / `blocked` / `unknown` / `unmeasured` として返す。
8. result に law id、evaluator id、basis refs、support atom refs、support molecule refs、detail refs、severity を付ける。
```

`measuredPass` は Lean theorem discharge ではない。`measuredViolation` は global architecture failure ではない。
どちらも `ArchMap + LawPolicy` の範囲で evaluator が計算した bounded diagnostic result である。

## ArchSig Evaluation Contract

ArchSig の計算順序は次である。

```text
1. ArchMap primary を validate する。
2. LawPolicy を validate する。
3. ArchSig normalizer が ArchMap primary を normalized ArchMap へ変換する。
4. unsupported atom は validation error とし、composition / required port が成立しない molecule を
   `blockedForNormalization` に分類する。
5. LawPolicy の各 policy entry の evaluator が normalized ArchMap と LawPolicy を読む。
6. typed evaluator result として `measuredPass` / `measuredViolation` / `blocked` / `unknown` /
   `unmeasured` を出す。
7. analysis packet / summary / viewer / distanceDiagnosis を typed evaluator result から作る。
```

ArchSig がしてはならないこと:

- source repository を直接読んで ArchMap を補完する。
- label / review memo / authoring note だけから positive result を出す。
- missing atom を measured zero にする。
- ArchMap primary にない molecule を勝手に生成する。
- obstruction / square / holonomy / risk を ArchMap input として扱う。

## Normalizer Contract

Normalizer は versioned registry によって動く。

Registry manifest は少なくとも次を公開する。

- normalizer id / version
- accepted atom kinds
- predicate vocabulary
- source ref requirements
- object / payload binding rules
- AtomKind / Axis mapping rules
- valence template refs
- generated molecule candidate criteria
- `blockedForNormalization` criteria
- negative fixtures that must not normalize

Normalizer output は ArchSig evaluator が読む typed computation input である。

```text
ArchMap atom:
  kind=capability subject=domain.OrderService predicate=placesOrder

Normalized atom candidate:
  kind=AtomKind.capability
  axis=Axis.static
  predicate=capability(domain.OrderService, placesOrder)
  status=normalized
```

## Removed v0 Fields

| Removed field | v1 replacement |
| --- | --- |
| `semanticObservations` | `semantic` atom -> `semantic.interpretation@1` normalizer -> semantic evaluator basis refs. Negative fixture: label-only semantic text does not normalize. |
| `projectionInfo` | projection is evaluator output from registry evaluator `projection.reading@1` over normalized atoms. Negative fixture: projection-only v0 field is validation failure. |
| `operationSquareEvidence` | square / commutation / holonomy are evaluator readings from normalized relations and molecule candidates. Negative fixture: square-only v0 field is validation failure. |
| `concernHints` | review notes may exist outside ArchMap as authoring notes, but are not diagnostic input. Negative fixture: concern-only artifact produces no measured result. |
| `observationGaps` | missing evidence is computed from evaluator requirements and atoms only. Negative fixture: authored gap list is ignored or rejected, never measured zero. |
| `nonConclusions` | boundary is carried by schema, manifest, and analysis output. Negative fixture: nonConclusion prose cannot create blocker or safe result. |

各 replacement は registry manifest に `replacementId`、required atom kinds、required molecule
membership、typed output packet refs、positive fixture、negative fixture を持つ。
削除 field を単に無視するだけの実装は acceptance を満たさない。

## Failure Contract

次は validation failure であり、`analyze` / `pr-review` は非ゼロ終了する。

- v0 ArchMap / LawPolicy を v1 input として渡す。
- v1 root に removed field、legacy alias、unknown root field が存在する。
- `sources`、atom refs、molecule refs が解決できない。
- atom `kind` が registry vocabulary に存在しない。
- `predicate` が active normalizer の vocabulary に存在しない。
- `subject` / `object` / payload refs が source table に解決できない。
- LawPolicy evaluator / basis が解決できない。
- label / review memo / authoring note だけが positive result の根拠になっている。

Validation failure 時、ArchSig は raw analysis packet、summary、viewer data を出さない。
出してよいのは validation report と failure manifest だけである。
既存 out-dir に古い success artifact がある場合、ArchSig は stale success artifact を削除するか、
failure manifest に stale artifact suppression status を記録し、今回 run の success artifact として読めないようにする。

## Implementation Plan

1. `archmap/v1` primary schema を `sources` / `atoms` / `molecules` に作り直す。
2. atom kind / predicate vocabulary を registry enum として実装する。
3. `law-policy/v1` を law / evaluator / basis / scope / severity selector として実装する。
4. versioned normalizer registry と removed field replacement registry を追加する。
5. normalized ArchMap artifact を追加する。
6. typed evaluator result artifact を追加する。
7. v0 reader、dual schema reader、legacy alias、compatibility shim を追加しない。
8. v0 fixture / golden packet equality を維持せず、v1 fixture / golden packet に置き換える。
9. `archsig_analysis_packet.rs` の v0 field 依存を normalized ArchMap + evaluator pipeline へ置き換える。
10. `analysis/distance/*` を typed evaluator result と normalized atoms ベースへ置き換える。
11. `concernHints` / `projectionInfo` / `operationSquareEvidence` 由来の positive reading を消す。
12. validation failure 時に stale success artifact が今回 run の output として読めないことを保証する。
13. practical example、minimal fixture、golden corpus、skills、README、website schema example を v1 に置き換える。
14. `analyze --strict-distance` で unknown / blocked / unmeasured が zero に落ちないこと、label-only / removed-field-only / schema-only reading が measured に昇格しないことを検査する。
15. `analyze --emit-raw-artifacts` の v1 fixture packet が FieldSig handoff / schema compatibility check を通ることを確認する。

## ArchSig Implementation Tasks

ArchSig 側の実装タスクは次である。これは LawPolicy を薄くした分を、ArchSig runtime の
versioned registry と typed evaluator pipeline として実装する作業である。

### 1. v1 input model / validation

- `ArchMapDocumentV1` を `sources` / `atoms` / `molecules` の primary model として追加する。
- `LawPolicyDocumentV1` を `policies[]` の selector model として追加する。
- v1 mode では v0 root field、legacy alias、unknown root field を hard validation error にする。
- unresolved source ref、unknown atom kind、unknown predicate、unknown evaluator、unknown pack、
  unresolved basis を analysis 前に止める。
- validation failure 時は packet / summary / viewer data を出さず、validation report / failure manifest
  だけを出す。

### 2. Normalizer registry

- atom constructor vocabulary を Rust enum として定義する。
- constructor ごとの required payload shape、source ref requirement、predicate vocabulary、
  `AtomKind` / `Axis` mapping、valence template ref を registry manifest に持たせる。
- valid ArchMap atom はすべて normalized atom presentation へ total に変換する。
- registry に mapping がない atom は silent drop せず validation error にする。
- molecule は explicit membership だけから generated molecule candidate に変換し、required port /
  composition condition が欠ける場合は `blockedForNormalization` にする。

### 3. Law / evaluator registry

- evaluator id / version を static registry として実装する。
- 各 evaluator manifest に law id、required atom constructors / predicates、required molecule condition、
  scope filtering rule、missing blocker rule、pass / violation criteria、typed result schema、
  distance contribution、summary / detail output refs、negative fixtures を持たせる。
- `solid@1` のような policy pack は registry-defined law entries へ展開する。
- LawPolicy の `policies[]` entry は evaluator / pack を選ぶだけにし、criteria、witness rule、
  axis rule、distance formula を上書きできないようにする。

### 4. Typed evaluator pipeline

- `ArchMap + LawPolicy` を直接 fat packet に流さず、
  `ArchMapDocumentV1 -> NormalizedArchMap -> TypedEvaluatorResult[]` の順に処理する。
- evaluator result は `measuredPass` / `measuredViolation` / `blocked` / `unknown` / `unmeasured`
  を first-class status として持つ。
- missing atom / molecule / source ref は measured zero にせず、evaluator manifest の blocker rule に従う。
- positive bounded conclusion は typed evaluator result、support refs、basis refs からだけ生成する。

### 5. Packet / distance / summary replacement

- `archsig_analysis_packet.rs` の v0 LawPolicy field 依存を typed evaluator result 参照に置き換える。
- `analysis/distance/*` は `part4DistanceProfile` ではなく evaluator registry の distance contribution と
  typed evaluator result から計算する。
- summary / viewer / detail index は v0 の `signatureAxes` / `obstructionCircuits` 前提を、
  typed evaluator result と derived packet refs 前提へ置き換える。
- `semanticObservations`、`projectionInfo`、`operationSquareEvidence`、`concernHints`、
  `observationGaps` 由来の positive readings を消す。

### 6. CLI / fixture / migration boundary

- `analyze` / `pr-review` の v1 path を追加し、v0 compatibility path は完了条件にしない。
- minimal fixture、practical fixture、SOLID fixture、negative fixture、golden packet を v1 で作り直す。
- `--strict-distance` は unknown / blocked / unmeasured、label-only、removed-field-only、schema-only reading を
  measured にしないことを検査する。
- release note / migration note に v1 が破壊的変更であること、v0 dual reader を持たないことを明記する。

## Acceptance Criteria

### ArchMap Authoring

- ArchMap primary は code-derived atom map として自然に書ける。
- ArchMap primary は `sources` / `atoms` / `molecules` を中心にする。
- atom は source-derived typed fact であり、自由自然文ではない。
- molecule は explicit author input であり、ArchSig が勝手に推測しない。
- ArchMap primary に obstruction、signature、distance、homotopy、risk、evidence gap、projection を置かない。

### AAT Compatibility

- Normalizer は atom kind を AAT-compatible `AtomKind` / `Axis` / typed predicate へ写す。
- Normalizer は source を再読込しない。
- Normalizer は valid ArchMap に対して決定論的かつ total である。
- valid ArchMap 内の atom はすべて normalized atom presentation を持つ。
- registry に mapping がない atom kind / predicate / shape は validation error である。
- generated molecule candidate は explicit molecule membership からだけ作る。
- generated molecule candidate は membership だけでなく、primitive atom presentation、finite configuration、
  composition graph、required port match がそろう場合だけ positive evaluator basis になる。
- incompatible pair または missing required port を含む molecule は `blockedForNormalization` または
  evaluator の `blocked` / `unknown` として扱い、`GeneratedMolecule` positive result に昇格しない。
- AAT-compatible presentation は computation artifact であり、ArchMap authoring schema ではない。

### LawPolicy / ArchSig

- LawPolicy は policy entries の law / evaluator / basis / scope / severity に絞られている。
- LawPolicy は registry-defined policy pack を選べる。
- SOLID は `solid@1` pack または 5つの明示的 law entries として表現できる。
- LawPolicy は witness / axis / missing blocker / obstruction / measurement DSL / score formula を持たない。
- Measurement、aggregation、threshold、distance contribution、review focus は evaluator registry が所有する。
- 各 law の計算手順は evaluator registry manifest に固定されている。
- LawPolicy の `policies[]` entry は pack / evaluator を選ぶだけで、law-specific criteria を上書きできない。
- ArchSig evaluator は normalized ArchMap と LawPolicy だけから diagnostic result を出す。
- ArchSig evaluator は Lean proof object、Lean theorem discharge、Lean runtime call を要求しない。
- Missing atom は measured zero にならない。
- Missing blocker は evaluator requirement、LawPolicy scope、atoms の照合からだけ生成される。
- Positive bounded conclusion は typed evaluator result、detail refs、evaluator basis refs からだけ生成される。

### Tests / Fixtures

- unknown atom kind、unknown predicate、unresolved source ref は validation error になる。
- valid ArchMap fixture の全 atom は normalized atom presentation を持つ。
- valid ArchMap の atom が normalizer で dropped / unnormalized にならない。
- label-only atom は measured result に昇格しない。
- removed v0 field only の fixture は validation failure または unmeasured result になり、measured result に昇格しない。
- molecule membership がない atom 集合から generated molecule candidate が勝手に作られない。
- composition graph を構成できない molecule、required port match が欠ける molecule は
  generated molecule candidate / positive result に昇格しない。
- evaluator が要求する atom / molecule / source ref がない fixture は `unknown` / `unmeasured` /
  `blocked` になり、measured zero にならない。
- validation failure の out-dir には今回 run の packet / summary / viewer が残らず、古い success artifact も
  今回 run の success として読めない。
- `SAFE_WITHIN_POLICY` / `NO_SELECTED_OBSTRUCTION` /
  `ACCEPTABLE_UNDER_EVIDENCE_CONTRACT` の positive fixture は evaluator basis refs を持つ。
- ArchSig v1 fixture / CLI tests は Lean runtime なしで実行できる。
- practical example、minimal fixture、CLI tests、strict-distance tests、schema catalog、skills、docs/tool、website/manual が v1 境界と一致している。
- v0 reader、dual schema reader、legacy alias、compatibility shim が存在しない。
- v0 fixture / golden packet equality は完了条件ではなく、v1 fixture / golden packet に置き換わっている。
- 後方互換性の欠如が release note / migration note に明記されている。

## Non-Goals

- ArchMap を AAT の formal input schema にする。
- ArchMap author に `AtomShape` / `AtomValence` / compatible composition を手書きさせる。
- ArchMap で obstruction circuit、lawfulness、zero curvature、distance、holonomy を表現する。
- LawPolicy を witness predicate DSL、axis DSL、missing blocker DSL、exactness DSL として扱う。
- LLM / tool が generated evaluation profile を作り、ArchSig がそれを計算規則として読む。
- ArchSig が source repository を直接読んで ArchMap を補完する。
- ArchSig を Lean 証明器、Lean theorem dispatcher、Lean proof object generator として扱う。
- ArchSig が hidden IR で semantic / projection / square / gap / concern を再生成する。
- missing atom を gap 一覧として ArchMap author に列挙させる。
- concern / review memo を diagnostic input として扱う。
- 既存 v0 artifact と packet equality を維持する。
- v0 runtime compatibility、dual reader、compatibility shim、legacy alias を維持する。
- FieldSig の longitudinal / forecast schema をこの PRD で再設計する。
