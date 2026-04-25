# ComponentUniverse validation report v0

Lean status: `empirical hypothesis` / tooling implementation.

この文書は Issue [#109](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/109)
の設計メモである。目的は、Sig0 / v1 extractor output と Lean の
`ComponentUniverse` の責務境界を検査する validation report の最小 schema と CLI
contract を固定することである。

Issue [#116](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/116)
で、Sig0 extractor output を入力にこの report を生成する
`sig0-extractor validate --input ...` を実装した。

ここで定義する report は Lean theorem ではない。extractor が現実コードベースから
作った JSON graph を、Lean 側の proof-carrying measurement universe に渡せる形へ
近づけるための tooling-side evidence である。`ComponentUniverse` の `Nodup`,
coverage, edge-closedness witness を Lean 上で構成したことは主張しない。

## 対象範囲

v0 report は Sig0 extractor output を入力にする。

- 入力 schema は `sig0-extractor-v0` を対象にする。
- component 粒度は extractor output の `componentKind` に従う。
- edge の向きは既存方針と同じく `source depends on target` とする。
- policy evaluation と empirical dataset の欠損値規約は既存の `metricStatus` を読む。
- report は JSON output の検査結果であり、source parser の完全性や repository 全体との
  一致は別の fixture / snapshot test の対象にする。

## ComponentUniverse との責務境界

Lean の `ComponentUniverse` は、明示された有限 universe 上で次を持つ
proof-carrying object である。

- component list が重複しないこと。
- graph vertex が universe に coverage されること。
- edge endpoint が universe 内に閉じていること。

validation report は、これらに対応する JSON-level check を出す。ただし JSON-level check
は Lean proof の代替ではない。たとえば `components` の id が重複しないことを report が
`pass` しても、それは Lean の `List.Nodup` witness を自動生成したことを意味しない。

Sig0 extractor v0 では、local Lean source file だけを `components` に列挙し、`Mathlib.*`
などの外部 import target は `edges` の target として残す場合がある。また
multi-project / sample layout では、`Foo/Main.lean` 由来の `Foo.Main` が root module
`Foo` を import し、source file component としては `Foo.Foo` のように表れることがある。
この `Foo` は source file coverage を伴わない synthetic module root target として扱い、
component list へ自動補完しない。このため report は universe mode を明示する。

| mode | 意味 | `ComponentUniverse` への読み替え |
| --- | --- | --- |
| `local-only` | `components` に列挙された local component だけを universe とする。外部 target または synthetic module root target を持つ edge は closure 対象から除外し、warning として数える。 | local projection 上の universe 候補。外部 edge や root target を含む graph 全体の witness ではない。 |
| `closed-with-external` | edge endpoint に現れる外部 node や synthetic root node も synthetic component として universe 候補に含める。 | graph closure の検査には使えるが、source file coverage とは別扱いにする。 |

v0 の既定 mode は `local-only` とする。

## 最小 JSON schema

report は単一 JSON document とし、schema version を必須にする。

```json
{
  "schemaVersion": "component-universe-validation-report-v0",
  "input": {
    "schemaVersion": "sig0-extractor-v0",
    "path": ".lake/sig0.json",
    "root": ".",
    "componentKind": "lean-module"
  },
  "universeMode": "local-only",
  "summary": {
    "result": "warn",
    "componentCount": 10,
    "localEdgeCount": 9,
    "externalEdgeCount": 2,
    "failedCheckCount": 0,
    "warningCheckCount": 1,
    "notMeasuredCheckCount": 2
  },
  "checks": [
    {
      "id": "component-id-nodup",
      "title": "component ids are duplicate-free",
      "result": "pass",
      "leanBoundary": "Nodup-like JSON evidence only"
    },
    {
      "id": "edge-closure-local",
      "title": "local dependency edges are closed over selected universe",
      "result": "pass",
      "leanBoundary": "edge-closedness candidate for local-only projection"
    },
    {
      "id": "external-edge-targets",
      "title": "external import targets are outside selected universe",
      "result": "warn",
      "count": 2,
      "examples": [
        {
          "source": "Formal.Arch.Matrix",
          "target": "Mathlib.Data.Matrix.Basic",
          "evidence": "import Mathlib.Data.Matrix.Basic"
        }
      ],
      "leanBoundary": "not a ComponentUniverse witness for the full import graph"
    },
    {
      "id": "boundary-policy-status",
      "title": "boundary violation metric is measured",
      "result": "not_measured",
      "reason": "policy file not provided",
      "metric": "boundaryViolationCount"
    }
  ],
  "warnings": [
    "local-only universe excludes external import targets"
  ]
}
```

### Top-level fields

| field | 型 | 必須 | 意味 |
| --- | --- | --- | --- |
| `schemaVersion` | string | yes | v0 では `component-universe-validation-report-v0` 固定。 |
| `input` | object | yes | 検査した extractor output の schema, path, root, component kind。 |
| `universeMode` | string | yes | `local-only` または `closed-with-external`。 |
| `summary` | object | yes | report 全体の集計。 |
| `checks` | list | yes | 個別 check の結果。 |
| `warnings` | list string | no | human-readable な補助 warning。 |

`summary.result` は `pass`, `warn`, `fail` のいずれかにする。`not_measured` check は
単独では `fail` にしないが、dataset へ渡すときは欠損値として扱う。

### Check result

各 check は少なくとも次を持つ。

| field | 型 | 必須 | 意味 |
| --- | --- | --- | --- |
| `id` | string | yes | stable check id。 |
| `title` | string | yes | check の短い説明。 |
| `result` | string | yes | `pass`, `warn`, `fail`, `not_measured` のいずれか。 |
| `reason` | string | no | `fail` / `not_measured` の理由。 |
| `count` | integer >= 0 | no | 該当 item 数。 |
| `examples` | list object | no | review 用の代表例。全件 dump ではなく上限を設ける。 |
| `metric` | string | no | `metricStatus` に対応する場合の axis 名。 |
| `leanBoundary` | string | no | Lean theorem ではなく tooling evidence である境界説明。 |

## v0 checks

v0 report は次の check を持つ。

| id | result 条件 | 目的 |
| --- | --- | --- |
| `schema-version-supported` | input schema が対応範囲なら `pass`、未対応なら `fail`。 | 古い JSON を暗黙に測定済み扱いしない。 |
| `component-id-nodup` | `components[].id` が重複しなければ `pass`、重複があれば `fail`。 | `Nodup` 相当の JSON-level evidence。 |
| `component-path-nodup` | path を持つ component の `path` が重複しなければ `pass`。 | 同一 file の二重 component 化を検出する。 |
| `edge-endpoint-resolved` | 各 edge の source / target が component, external node, synthetic module root target のいずれかに分類できれば `pass`。 | coverage / closure check の前提を固定する。 |
| `edge-closure-local` | `local-only` mode で local endpoint の edge が components 内に閉じていれば `pass`。synthetic module root target は closure 対象から除外する。 | local projection の edge-closedness 候補を検査する。 |
| `external-edge-targets` | 外部 target または synthetic module root target があれば `warn`、なければ `pass`。 | full import graph の witness と混同しない。 |
| `metric-status-complete` | signature 全軸に `metricStatus` entry があれば `pass`、欠けていれば `warn`。 | 未評価軸を risk 0 と混同しない。 |
| `boundary-policy-status` | `boundaryViolationCount` が測定済みなら `pass`、policy 未指定なら `not_measured`。 | boundary 軸の欠損値を明示する。 |
| `abstraction-policy-status` | `abstractionViolationCount` が測定済みなら `pass`、policy 未指定なら `not_measured`。 | abstraction 軸の欠損値を明示する。 |
| `extractor-warning-status` | extractor output に warning がなければ `pass`、warning があれば `warn`。 | parser / selector の不確実性を dataset 側へ渡す。 |

`metric-status-complete` は後方互換のため `warn` にとどめる。ただし empirical dataset へ
取り込む adapter は、欠けた entry を `measured = false` として補完し、理由を
`legacy data without metricStatus entry` のように明示する。

## CLI contract

report 生成の最小 CLI contract は次とする。

```bash
sig0-extractor validate \
  --input .lake/sig0.json \
  --out .lake/sig0-validation.json \
  --universe-mode local-only
```

`--out` を省略した場合は stdout に report を出力する。`--universe-mode` を省略した場合は
`local-only` とする。

終了コードは次で固定する。

| exit code | 条件 |
| --- | --- |
| 0 | `summary.result` が `pass` または `warn`。JSON report は生成されている。 |
| 1 | `summary.result` が `fail`。JSON report は生成できている。 |
| 2 | 入力 JSON を読めない、または report schema を生成できない。 |

CI で gating する場合は、当面 `fail` だけを失敗扱いにする。`warn` と `not_measured` は
dataset 側の欠損値・除外条件として扱い、Lean proof の成否とは分離する。

## Empirical dataset への接続

empirical dataset record は、Signature snapshot の補助 metadata として validation report
への参照を持てる。

```text
SignatureSnapshot.validationReport =
  path: String
  schemaVersion: "component-universe-validation-report-v0"
  summaryResult: "pass" | "warn" | "fail"
  universeMode: "local-only" | "closed-with-external"
```

H1 から H5 の主要分析では、`summaryResult = fail` の snapshot を除外する。
`summaryResult = warn` の snapshot は、warning 種別を stratification または sensitivity
analysis に使う。`not_measured` metric は既存の `metricStatus` と同じく欠損値であり、
placeholder 0 を risk 0 として扱わない。

## 実装方針

最初の実装は既存 Sig0 extractor output だけを読む pure validation pass とする。source
file を再 scan せず、入力 JSON に含まれる `components`, `edges`, `signature`,
`metricStatus`, 将来の `warnings` field だけから report を作る。

追加実装は次の順で進める。

1. `sig0-extractor validate --input ...` で schema / duplicate / edge classification を
   検査する。
2. `metricStatus` completeness と boundary / abstraction policy status を report に載せる。
3. policy file 適用後の violation evidence と report の check id を接続する。
4. empirical dataset builder が `validationReport` summary を snapshot metadata に保存する。

この順序なら、Lean 側の `ComponentUniverse` 定義を変更せずに、extractor output の
責務境界を段階的に検査できる。
