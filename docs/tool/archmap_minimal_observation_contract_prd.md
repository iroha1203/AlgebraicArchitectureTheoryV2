# ArchMap Minimal Observation Contract PRD

この PRD は、ArchMap schema を最小の observation contract へ戻すための
破壊的再設計要求を定義する。

既存の `archmap-observation-map-v0` は、実装を重ねる中で、ArchSig の計算を楽にする
補助 field を ArchMap 側へ押し戻しすぎた。`semanticObservations`、`projectionInfo`、
`operationSquareEvidence`、`concernHints`、`observationGaps`、大量の
`nonConclusions` は、それぞれに理由があったが、結果として ArchMap が
「観測した Atom / Molecule の地図」ではなく、分析前の濃い報告書になっている。

この PRD では後方互換性を維持しない。既存 schema、fixture、validation、analysis packet
builder、skill、docs、website surface は壊してよい。優先するのは、元の責務分離である。

```text
ArchMap:
  source universe から観測した atoms と molecules だけを書く。

LawPolicy:
  repository が採用する policy と、それを読む ArchSig evaluator を選ぶ。

ArchSig:
  built-in versioned evaluator library で ArchMap を評価し、bounded diagnostic conclusion を出す。
```

ArchMap は AAT に渡す数学スキーマではない。ArchMap は source-grounded observation contract
である。ArchSig は Lean 証明器ではない。ArchSig は、与えられた
`ArchMap + LawPolicy + evidence contract` から語れることだけを語る。

## 中心責務

ArchMap の責務は次の問いに答えることだけである。

```text
この source universe の中で、どの atoms と molecules が観測されたか。
```

ArchMap は次を答えない。

- どの projection が AAT object へ対応するか。
- どの operation square が成立するか。
- どの obstruction circuit があるか。
- どの concern が risk / violation へ昇格するか。
- 何が観測されなかったかの網羅的リスト。
- global architecture truth、lawfulness、zero curvature、semantic correctness。

書かれている atom / molecule だけが観測済みである。書かれていないものは unknown であり、
measured zero でも gap でもない。

## R0. 破壊的変更を前提にする

この PRD で許容する破壊的変更は、ArchMap input / authoring contract 側の破壊である。
ArchSig output の診断品質、測定深度、読解可能性を落としてよいという意味ではない。

この PRD の実装では、次の input-side 互換性を維持しない。

- `archmap-observation-map-v0`
- `semanticObservations`
- `projectionInfo`
- `operationSquareEvidence`
- `concernHints`
- `observationGaps`
- v0 fixture / golden packet equality
- v0 ArchMap validation report shape
- v0 skill prompt output shape
- v0 website / manual schema examples

互換 shim、dual reader、legacy field alias は完了条件にしない。必要なら migration note は
書いてよいが、runtime compatibility は要求しない。

一方で、ArchSig output は現行の bounded diagnostic conclusion と同等以上の品質を維持する。
ArchMap を痩せさせた結果として、obstruction、signature、distance、homotopy、coverage、
review focus が粗くなる実装は完了とみなさない。v0 の補助 field に依存していた reading は、
削除された field を復活させるのではなく、観測済み atom / molecule と ArchSig evaluator library
から同等以上に評価できるよう作り直す。

## 設計原則: evaluator first

この再設計は schema first ではない。ArchMap schema を削る前に、ArchSig が何を計算単位にするかを
固定する。

```text
ArchMap v1:
  typed observed atom graph + molecule membership。

LawPolicy v1:
  repository policy selection + basis refs + evaluator refs。
  witness predicate、signature axis、coverage rule、exactness assumption を持たない。

ArchSig v1:
  versioned evaluator library を持つ。
  evaluator が witness / axis / coverage / zero-reading rule を実装として所有する。
```

LawPolicy に計算自由度を置かない。LawPolicy が任意の witness predicate や axis valuation rule を
持つと、ArchMap から削った補助 field が LawPolicy 側に再発生する。LLM / tool がそれを生成する設計も
採用しない。生成精度に ArchSig の計算が引っ張られるためである。

ArchSig evaluator は固定 ID と version を持つ。

```text
solid.dependency-inversion@1
domain.no-direct-infra-dependency@1
provider.output-validation-before-persistence@1
transaction.repository-owns-boundary@1
```

各 evaluator は、必要な AAT atom family、観測 relation、molecule membership、source ref kind、
coverage blocker、signature axis、distance contribution をコードとして定義する。ArchMap は evaluator
を助けるための derived field を持たない。LawPolicy は evaluator を発明しない。

各 evaluator は registry manifest を持つ。manifest は少なくとも次を公開する。

```text
evaluator id / version
recognized atom families
recognized relations
required term/ref shapes
measured criteria
blocked / unknown criteria
output reading families
packet ref paths emitted on success
negative fixtures that must not measure
```

Output quality は「現行と同等」という抽象 claim だけで判定しない。削除対象 field または output
reading family ごとに、次の対応表を実装 PR の acceptance に含める。

```text
removed v0 input / reading family
-> replacement evaluator id
-> required observed atoms / molecules / refs
-> measured / blocked / unknown criteria
-> output packet refs
-> negative test fixture
```

ArchSig の計算は次の順序で行う。

```text
1. ArchMap を lookup index にする。
2. LawPolicy の selected evaluator refs を読む。
3. 各 evaluator を ArchMap index に対して実行する。
4. evaluator result を measured / blocked / unknown / notApplicable に分類する。
5. measured result だけから obstruction、signature、distance、homotopy、review focus を作る。
```

不足した観測は measured zero ではない。evaluator が要求する atom / molecule / source ref が
存在しない場合、ArchSig はその evaluator result を blocked / unknown / unmeasured にする。

## R1. ArchMap v1 は sources / atoms / molecules だけを primary schema にする

ArchMap v1 の primary shape は次である。

```json
{
  "schema": "archmap/v1",
  "id": "practical-rust-service",
  "sources": {
    "app": { "kind": "file", "path": "sample/src/app.rs" },
    "app.place_order": {
      "kind": "symbol",
      "source": "app",
      "symbol": "place_order",
      "line": 23
    },
    "domain.OrderService": {
      "kind": "symbol",
      "source": "app",
      "symbol": "OrderService"
    },
    "domain.Order": {
      "kind": "symbol",
      "source": "app",
      "symbol": "Order"
    }
  },
  "atoms": [
    {
      "id": "a:place-order",
      "family": "capability",
      "relation": "provides",
      "terms": ["domain.OrderService", "domain.Order"],
      "refs": ["app.place_order"],
      "label": "OrderService places an order"
    }
  ],
  "molecules": [
    {
      "id": "m:place-order-flow",
      "atoms": ["a:place-order", "a:inventory-check", "a:reserve-effect"],
      "refs": ["app.place_order"]
    }
  ]
}
```

`sources` は source 台帳である。file path、symbol、line、doc section、runtime trace などは
ここに一度だけ書く。Atom / Molecule は `refs` で source id を参照する。Atom / Molecule に
file path を直接繰り返さない。

`sources` は読んだ source の台帳であり、未読 source の inventory ではない。private、
unavailable、out-of-scope の列挙は ArchMap primary schema に持ち込まない。必要な場合は
run manifest、authoring note、または ArchSig evaluator の coverage result として扱う。

## R2. Atom family は AAT core family に準拠する

Atom は「観測された原子的事実」である。Atom は canonical Atom truth ではなく、
source-grounded observation である。

ArchMap v1 の atom family は AAT 数学本文の core Atom family に準拠する。PRD や実装都合で
Atom family を追加・削除・分割しない。特に、semantic Atom と runtime interaction Atom は
AAT core family の一部であり、ArchSig が静的解析器へ退化しないための必須語彙である。

Source kind、runtime trace kind、evidence boundary、review memo は Atom family ではない。
これらを Atom family に混ぜると、AAT の Atom ontology と ArchSig evaluator の軸がずれる。

Atom は prose triple ではない。ArchSig が計算に使う部分は `family`、`relation`、`terms`、`refs`
だけである。`label` は人間向け表示であり、evaluator は `label` を読まない。

- `family`: AAT core Atom family。
- `relation`: ArchSig evaluator library が認識する controlled relation。
- `terms`: `sources` の id または既存 atom id への参照。自然文でも未解決 namespace でもない。
- `refs`: source 台帳への参照。
- `label`: 任意の表示用説明。

`terms` に未解決の `t:*` 文字列を許さない。計算対象となる概念、symbol、doc section、runtime trace は
`sources` に登録し、Atom はその source id を参照する。Atom 間の関係を観測する場合だけ、`terms` に
atom id を含めてよい。

`relation` は versioned evaluator registry が公開する relation vocabulary に含まれる必要がある。
未知 relation は測定不能として黙って落とすのではなく、ArchMap validation error にする。`label` を
変更しても evaluator result が変わらない negative test を必須にする。

例:

```json
{
  "id": "a:reservation-meaning",
  "family": "semantic",
  "relation": "represents",
  "terms": ["domain.InventoryReservation", "domain.Order"],
  "refs": ["domain.InventoryReservation"],
  "label": "InventoryReservation represents reserved inventory bound to an order"
}
```

Atom に `confidence`、`uncertainty`、`nonConclusions` を標準搭載しない。必要な reviewer memo は
ArchMap 本体ではなく authoring artifact に置く。ArchSig の測定境界は、selected evaluator と
analysis output で表現する。

## R3. Molecule を観測された atom の束として強くする

Molecule は診断結果ではない。Molecule は、source-grounded atoms を束ねた観測単位である。
Lean 側の AAT でも、Molecule は既存 Atom の有限 configuration であり、role、pattern、
workflow そのものではない。

ArchMap v1 は molecule kind enum を持たない。kind にないものが表現できなくなる設計は採用しない。
Molecule の `atoms` は atom id の参照であり、配列は観測された finite configuration の membership
として読む。

Operation square、path candidate、homotopy candidate を ArchMap に first-class field として
置かない。Role、pattern、workflow、path-like reading は、ArchSig evaluator が molecule の
membership と source refs を読んで与える interpretation であり、ArchMap primary schema の
closed enum ではない。

```json
{
  "id": "m:reservation-sequence",
  "atoms": [
    "a:inventory-check",
    "a:reserve-effect",
    "a:reservation-created"
  ],
  "refs": ["app.place_order", "store.reserve"]
}
```

ArchSig は molecule を selected evaluator に従って読む。ArchSig は、
観測されていない reverse path、square、filler、risk cue を勝手に作らない。足りない場合は
blocked / unknown とする。

## R4. 次の field を ArchMap primary schema から削除する

### `semanticObservations`

`semanticObservations` という ArchMap 独自 layer は置かない。Semantic は AAT core Atom family
に属する。複数 Atom から読まれる意味は molecule に対する後段 interpretation として扱う。

### `projectionInfo`

Projection は ArchMap の観測ではない。ArchSig output の reading として作る場合も、
Atom / Molecule を直接根拠にする。ArchMap に `projectionInfo` を要求しない。

### `operationSquareEvidence`

Square は ArchMap の観測単位ではない。観測できるのは operation、state/effect、contract、
runtime interaction、またはそれらを含む molecule である。Square / commutation / holonomy /
obstruction への読みは LawPolicy + ArchSig の責務である。

### `concernHints`

Concern は ArchMap の primary input にしない。Review note として別 artifact に置くことは
許されるが、ArchSig は concern-only で obstruction、nonzero distance、holonomy、risk を
出してはならない。

### `observationGaps`

ArchMap に gap 台帳を持たせない。書かれていないものは unknown である。

Coverage gap は selected evaluator が要求する AAT atom family、relation、molecule membership、
source ref、policy basis が存在しないとき、ArchSig が deterministic に評価結果として出す。
これは「推測」ではなく、選ばれた policy requirement と観測集合の照合である。

### `nonConclusions`

ArchMap 本体に defensive prose を積まない。ArchMap の責務は schema の狭さで守る。
必要な boundary は docs、manifest、analysis output に置く。

## R5. ArchSig は hidden IR を作らず、atom / molecule を直接評価する

ArchSig は、ArchMap v1 を受け取って fat v0 相当の hidden IR を再構成してはならない。

許されるのは lookup index だけである。

```text
sources_by_id
atoms_by_id
atoms_by_family
atoms_by_relation
atoms_by_term
molecules_by_id
molecules_by_atom
```

禁止する hidden IR:

- synthetic semantic observations
- synthetic projection info
- inferred operation square evidence
- inferred concern hints
- inferred observation gaps
- guessed workflow / path / filler / reverse operation

ArchSig evaluator は `atoms`、`molecules`、`LawPolicy` を直接読む。ただし、LawPolicy から
witness predicate を受け取らない。witness / axis / coverage rule は built-in evaluator が所有し、
atom family、relation、terms、molecule membership、source refs に対して deterministic に実行する。

分析に必要な witness が見つからない場合、ArchSig は次のいずれかを返す。

- `blockedByCoverage`
- `unmeasured`
- `unknown`
- `notApplicableUnderSelectedPolicy`

未観測を `measuredZero` にしない。

## R6. LawPolicy は evaluator selector に絞る

LawPolicy は、対象 repository / organization / review context が採用する architecture policy と、
それを読む ArchSig evaluator を選ぶ artifact である。LawPolicy は計算言語ではない。

たとえば「この repository は SOLID を採用している」「domain layer は infrastructure へ直接依存しない」
「repository が transaction boundary を所有する」「external provider output は検証してから永続化する」
といった規約は、LawPolicy の selected policy になる。

LawPolicy v1 の primary shape は次である。

```json
{
  "schema": "law-policy/v1",
  "id": "practical-rust-service-policy",
  "selected": [
    {
      "policy": "domain.no-direct-infra-dependency",
      "evaluator": "domain.no-direct-infra-dependency@1",
      "basis": ["docs.architecture.layering"],
      "scope": ["src/domain/**"],
      "severity": "review-blocking"
    }
  ]
}
```

LawPolicy に次を置かない。

- selected design law refs
- generated selected signature axis refs
- generated witness predicates
- generated required observation shapes
- generated coverage requirements
- exactness assumptions
- obstruction circuit definitions
- molecule patterns

これらは LawPolicy authoring artifact でも LLM-generated profile でもない。ArchSig evaluator
library の実装である。

LawPolicy の `basis` は、policy が採用済みである根拠を指す。これは code source ref ではなく、
repository docs、organization rule、明示的な user approval などの policy basis である。
反復パターンや現在のコード形状だけを basis にして selected policy を作らない。根拠がない場合は
selected policy ではなく unresolved question として扱い、ArchSig の計算には入れない。

`evaluator` と `basis` は fail-closed に解決する。unknown evaluator id、unsupported evaluator
version、重複 evaluator id / version、未解決 basis、code-shape-only basis は analysis 前の hard
validation error である。これらを `unknown`、`unmeasured`、`blocked` として分析続行してはならない。
`blocked` は、既知 evaluator が選択され、policy basis も解決済みだが、要求観測が足りない場合だけに使う。

Operation square、homotopy、distance、curvature などの高次 reading は、selected evaluator が
観測済み atom / molecule に対して固定計算を実行した結果として評価する。ArchSig は候補を増やして
測定深度を見せかけない。

## R7. Failure contract は fail-closed にする

破壊的 input redesign では、invalid input を partial analysis にしてはならない。

次は validation failure であり、`analyze` / `pr-review` は非ゼロ終了する。

- `archmap-observation-map-v0` または `law-policy-v0` を v1 input として渡す。
- v1 root に removed field、legacy alias、unknown root field が存在する。
- Atom `family`、`relation`、`terms`、`refs`、molecule atom ref が解決できない。
- LawPolicy selected evaluator id / version が registry に存在しない。
- LawPolicy basis が explicit repository / organization rule または user approval に trace できない。
- `label`、review memo、authoring note だけが positive reading の根拠になっている。

Validation failure 時、ArchSig は raw analysis packet、summary、viewer data を出さない。出してよいのは
validation report と failure manifest だけである。既存 out-dir に古い success artifact がある場合も、
今回の失敗を success artifact と混同できないよう manifest に failure status を明示する。

## R8. 実装移行要求

実装は段階的に見えてもよいが、互換維持を目的にしない。

1. `archmap/v1` schema を追加し、v0 field を primary schema から削除する。
2. `tools/archsig/src/schema/archmap.rs` を sources / atoms / molecules 中心に作り直す。
3. Atom schema を prose triple ではなく `family` / `relation` / `terms` / `refs` / optional
   `label` にする。ArchSig evaluator は `label` を読まない。
4. ArchMap validation を、source id 解決、atom id 一意性、AAT core atom family 準拠、
   evaluator registry relation 準拠、term refs 解決、molecule atom refs、refs 解決に絞る。
5. `law-policy/v1` schema を evaluator selector として追加し、v0 の witness rule / axis /
   coverage / obstruction definition を primary schema から削除する。
6. ArchSig に versioned evaluator registry を追加する。各 evaluator は必要 atom family、relation、
   molecule membership、coverage blocker、axis valuation、distance contribution、output packet refs、
   negative fixture refs を実装または manifest で持つ。
7. LawPolicy validation は evaluator id / version、basis refs、scope、severity を fail-closed に検査する。
8. CLI は v0 input、removed fields、unknown fields、unknown evaluator、bad basis を非ゼロ終了にする。
9. Failure run は validation report と failure manifest だけを出し、raw packet / summary / viewer data を
   出さない。
10. `archsig_analysis_packet.rs` の v0 field 依存を削除し、selected evaluator execution pipeline へ
   作り直す。
11. `analysis/distance/*` は observation gap や projection info ではなく、evaluator result status と
   observed atom / molecule membership を根拠にする。
12. `operationSquareCandidates` は selected evaluator が観測済み molecule / relation から測定できる
   場合だけ構成する。観測されていない pair を総当たりで inferred candidate にしない。
13. `concernHints` 由来の positive reading を完全に消す。
14. v0 補助 field に依存していた output reading は、削除によって消すのではなく、
   atom / molecule direct evaluator と versioned evaluator library で同等以上の診断品質を保つ。
15. 削除対象 field / output reading family ごとに evaluator replacement table を docs と tests に置く。
16. practical example、minimal fixture、golden corpus、skills、README、website schema example を
   v1 に置き換える。
17. `analyze --strict-distance` は、unknown / blocked / unmeasured が zero に落ちていないこと、
   proxy/schema-only/label-only/removed-field-only readings が measured に昇格していないこと、
   summary / raw packet / `distanceDiagnosis` / `DiagnosticScope` が同期していることを検査する。
18. `analyze --emit-raw-artifacts` の v1 fixture packet が FieldSig handoff / schema compatibility check を
   通ることを確認する。

## Acceptance Criteria / 完了条件

- 極小 example の ArchMap が 100 行程度で、source 台帳、atoms、molecules だけで読める。
- Atom の計算 payload は `family` / `relation` / `terms` / `refs` であり、自然言語 `label` は
  evaluator に読まれない。
- Atom `terms` は `sources` の id または既存 atom id に解決され、未解決 `t:*` namespace や自然文を
  許さない。
- `relation` は versioned evaluator registry が公開する vocabulary に含まれ、未知 relation は
  ArchMap validation error になる。
- `label` を変更しても evaluator result、distance、obstruction、signature、coverage status が変わらない
  negative fixture が存在する。
- ArchMap v1 primary schema に `semanticObservations`、`projectionInfo`、
  `operationSquareEvidence`、`concernHints`、`observationGaps`、`nonConclusions` が存在しない。
- Atom family は AAT 数学本文の core Atom family に準拠し、semantic Atom と runtime interaction
  Atom を落とさない。
- Molecule は固定 kind enum を持たず、観測された Atom membership と source refs だけを primary
  payload とする。
- Workflow / path-like source reading は molecule kind ではなく、observed molecule に対する
  ArchSig evaluator interpretation として扱われる。
- ArchSig は v1 ArchMap を v0 相当の hidden IR へ変換しない。
- ArchSig 内部で許される中間構造は lookup index だけである。
- LawPolicy v1 は selected policy / evaluator / basis / scope / severity に絞られている。
- LawPolicy v1 に witness predicate、signature axis、coverage requirement、exactness assumption、
  obstruction circuit definition、molecule pattern が存在しない。
- selected policy は explicit repository / organization rule または user approval に trace できる。
- ArchSig は versioned evaluator registry を持ち、LawPolicy はその evaluator を選ぶだけである。
- evaluator は atom family、relation、terms、molecule membership、source refs を直接読む。
- evaluator registry は id / version、recognized families、relations、required term/ref shapes、
  measured / blocked / unknown criteria、output packet refs、negative fixture refs を公開する。
- unknown evaluator id、unsupported evaluator version、重複 evaluator id / version、未解決 basis、
  code-shape-only basis は analysis 前の hard validation error になる。
- `blocked` は、既知 evaluator と解決済み basis のもとで要求観測が足りない場合にだけ使われる。
- 削除対象 v0 field または output reading family ごとに、replacement evaluator、required observations、
  measured / blocked / unknown criteria、output packet refs、negative fixture が対応表として存在する。
- 追加 field がないために計算できない reading は、推測生成せず blocked / unknown / unmeasured になる。
- v0 input、removed field、legacy alias、unknown root field は validator、`analyze`、`pr-review` の各入口で
  fail-closed に拒否され、非ゼロ終了と validation report check id を持つ。
- `observationGaps` 削除後も、未観測が measured zero に落ちない。
- `concernHints` 削除後も、concern-only obstruction / distance / holonomy が生成されない。
- `projectionInfo` 削除後も、ArchSig output は observed atoms / molecules を根拠にした reading
  だけを出す。
- `operationSquareEvidence` 削除後も、selected evaluator が測定できる observed molecule / relation が
  ない square / path / filler は inferred されない。
- `concernHints` only、`projectionInfo` only、`operationSquareEvidence` only、missing molecule refs、
  label-only relation の negative fixtures が strict mode で measured に昇格しない。
- Validation failure 時は validation report と failure manifest だけを出し、raw analysis packet、
  summary、viewer data を出さない。
- ArchMap input は破壊的に痩せているが、ArchSig output の bounded diagnostic conclusion、
  measurement basis、coverage blocker、review focus の品質は現行より落ちていない。
- practical example、minimal fixture、CLI tests、strict-distance tests、schema catalog、skills、
  docs/tool、website/manual が v1 境界と一致している。
- `analyze --emit-raw-artifacts` の v1 fixture packet が FieldSig handoff / schema compatibility check を
  通る。
- 後方互換性の欠如が release note / migration note に明記されている。

## Non-Goals

- ArchMap を AAT の formal input schema にする。
- ArchMap で obstruction circuit、lawfulness、zero curvature、distance、holonomy を表現する。
- LawPolicy を witness predicate DSL、axis DSL、coverage DSL、exactness DSL として扱う。
- LLM / tool が generated evaluation profile を作り、ArchSig がそれを計算規則として読む。
- ArchSig が source repository を直接読んで ArchMap を補完する。
- ArchSig が hidden IR で semantic / projection / square / gap / concern を再生成する。
- 未観測を gap 一覧として ArchMap author に列挙させる。
- concern / review memo を diagnostic input として扱う。
- 既存 v0 artifact と packet equality を維持する。
- FieldSig の longitudinal / forecast schema をこの PRD で再設計する。
