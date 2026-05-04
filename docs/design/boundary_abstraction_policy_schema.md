# boundary / abstraction policy v0 schema

Lean status: `empirical hypothesis` / tooling design.

この文書は Issue [#106](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/106)
の設計メモである。目的は、extractor tooling が `boundaryViolationCount` と
`abstractionViolationCount` を測るための最小 policy file schema と counting unit を
固定することである。

ここで定義する policy file は Lean の `ComponentUniverse` を生成する証明ではない。
extractor は現実コードベースの component と dependency edge を測定し、policy に対する
violation count と evidence を出力する。Lean 側は、明示された有限 universe 上の
`ArchitectureSignature` や bridge theorem を扱う。policy coverage、selector の解決、
実コードベースとの一致は tooling-side evidence と実証研究の対象である。

## 対象範囲

v0 policy は静的依存グラフを対象にする。

- edge の向きは既存方針と同じく `source depends on target` とする。
- counting unit は extractor output の unique dependency edge である。
- boundary policy は「どの component group からどの component group へ依存してよいか」を
  allow-list として表す。
- abstraction policy は「client が concrete implementation へ直接依存せず、指定された
  abstraction component を経由すべき関係」を表す。
- runtime edge metadata, failure mode, timeout, circuit breaker coverage は対象外である。

## 最小 JSON schema

policy file は単一 JSON document とし、schema version を必須にする。

```json
{
  "schemaVersion": "signature-policy-v0",
  "policyId": "aatv2-local-policy",
  "componentIdKind": "lean-module",
  "selectorSemantics": "exact-or-prefix-star",
  "boundary": {
    "groups": [
      {
        "id": "formal-arch",
        "components": ["Formal.Arch.*"]
      },
      {
        "id": "entrypoint",
        "components": ["Formal", "Main"]
      }
    ],
    "allowedDependencies": [
      {
        "sourceGroup": "entrypoint",
        "targetGroup": "formal-arch",
        "reason": "entrypoint may depend on formal library"
      },
      {
        "sourceGroup": "formal-arch",
        "targetGroup": "formal-arch"
      }
    ],
    "unmatchedComponent": "not-measured"
  },
  "abstraction": {
    "relations": [
      {
        "id": "payment-port",
        "abstraction": "PaymentPort",
        "clients": ["OrderService", "CheckoutWorkflow"],
        "implementations": ["StripePaymentAdapter", "PaypalPaymentAdapter"],
        "allowedDirectImplementationDependencies": []
      }
    ],
    "unmatchedComponent": "ignore"
  }
}
```

### Top-level fields

| field | 型 | 必須 | 意味 |
| --- | --- | --- | --- |
| `schemaVersion` | string | yes | v0 では `signature-policy-v0` 固定。 |
| `policyId` | string | yes | dataset の `policyVersion` や extractor metadata に残す policy 識別子。 |
| `componentIdKind` | string | yes | selector が参照する component id の種類。v0 で予約する値は `lean-module`, `python-module`, `path`, `package`。 |
| `selectorSemantics` | string | yes | v0 では exact match と末尾 `*` prefix match だけを許す。 |
| `boundary` | object | no | boundary violation count を測る場合に必須。 |
| `abstraction` | object | no | abstraction violation count を測る場合に必須。 |

`selectorSemantics = "exact-or-prefix-star"` では、`Formal.Arch.*` は
`Formal.Arch.` prefix を持つ component id に一致する。`*` は末尾にだけ置ける。
正規表現や否定 selector は v0 では扱わない。複雑な分類が必要な repository では、
extractor 側で component id を正規化してから policy に渡す。

### Python module id policy

`componentIdKind = "python-module"` は、selector が Python の importable module id を
参照することを表す。Python v0 の component id は、明示された package root からの
相対 path を `.` 区切り module 名へ正規化した値である。

| file path | package root | component id |
| --- | --- | --- |
| `src/app/service.py` | `src` | `app.service` |
| `src/app/__init__.py` | `src` | `app` |
| `tests/test_service.py` | repository root | `tests.test_service` |

Python policy では repository root、source root、package root を分けて扱う。

| root | 役割 |
| --- | --- |
| repository root | checkout と artifact path の基準。component id の直接の基準にはしない。 |
| source root | scan 対象 file を制限する file system 境界。複数指定できる。 |
| package root | local import 解決と component id 正規化の基準。 |

`src/` layout では、通常 `sourceRoot = "src"` かつ `packageRoot = "src"` とする。
monorepo や multi-package repository では、package root ごとに測定単位を分けるか、
extractor output に root ref を残してから policy selector を評価する。namespace package は
明示された package root 群に属する file だけを local component とし、root 群の外にある
同名 namespace fragment は external dependency edge として扱う。

`tests/`, `test/`, `*_test.py`, `test_*.py` は既定では `python-module` component に含めてよい。
ただし production graph と test graph を分けたい repository では、次のように policy group
で分離する。

```json
{
  "componentIdKind": "python-module",
  "selectorSemantics": "exact-or-prefix-star",
  "boundary": {
    "groups": [
      { "id": "app", "components": ["app.*"] },
      { "id": "tests", "components": ["tests.*"] }
    ],
    "allowedDependencies": [
      { "sourceGroup": "tests", "targetGroup": "app" },
      { "sourceGroup": "app", "targetGroup": "app" }
    ],
    "unmatchedComponent": "not-measured"
  }
}
```

Python import edge の分類規約は次である。

- `source` と `target` が同じ package root 内の component id に解決できる場合、local module edge として boundary / abstraction policy の測定対象にする。
- `target` が package root 外、標準 library、installed dependency、または unresolved import の場合、external dependency edge として扱い、local boundary count には含めない。
- relative import は source module の package context と package root から正規化する。正規化できない場合は unresolved external edge とし、extractor warning に残す。
- dynamic import, plugin loading, framework convention, generated module, notebook 由来の依存は v0 の静的 import graph では未測定であり、測定済み 0 とは読まない。

この policy は extractor evidence の contract であり、Lean `ComponentUniverse` の
coverage / edge-closedness witness、実コード extractor の完全性、または
architecture lawfulness を主張しない。

## boundary policy

`boundary.groups` は component set に名前を付ける。v0 の測定では、測定対象 local
component はちょうど 1 つの boundary group に属する必要がある。0 個または複数 group に
一致する component がある場合、`boundaryViolationCount` は測定済みとしない。

`boundary.allowedDependencies` は group 間の allow-list である。extractor は各 dependency
edge `(source, target)` について source group と target group を求め、対応する
`allowedDependencies` entry がなければ boundary violation として記録する。

counting rule:

- 1 unique dependency edge を最大 1 violation として数える。
- 同じ edge に複数 evidence line があっても count は 1 にする。
- self edge は extractor output に現れる場合も通常の edge として扱い、allow-list に従う。
- 外部 dependency は、component list に含まれない target として出力される限り
  boundary count の対象外にし、必要なら evidence metadata に残す。
- `unmatchedComponent = "not-measured"` の場合、未分類 component があると
  `metricStatus.boundaryViolationCount.measured = false` とする。

policy が存在し、全 local component が一意に分類され、すべての measured local edge が
評価できた場合だけ、`boundaryViolationCount = 0` を「測定された違反なし」と読める。

## abstraction policy

`abstraction.relations` は、client、abstraction、implementation の対応を列挙する。
v0 では、client component が implementation component へ直接依存する edge を
abstraction violation として扱う。client が abstraction component へ依存することを
強制する complete check はここでは行わない。complete check は将来の validation report
または projection bridge 側で扱う。

counting rule:

- 1 unique dependency edge が 1 つ以上の abstraction relation に違反する場合、
  `abstractionViolationCount` には 1 回だけ加算する。
- 違反した relation id の一覧は evidence metadata に残してよい。
- `allowedDirectImplementationDependencies` に target が含まれる edge は違反にしない。
- unresolved selector や空の `clients` / `implementations` がある場合、その relation は
  schema violation とし、`abstractionViolationCount` は測定済みとしない。
- `abstraction.relations` が空または `abstraction` が未指定の場合、
  `abstractionViolationCount` は未評価であり、placeholder 0 を risk 0 と読まない。

この軸は `ProjectionSound` や `ProjectionExact` の Lean theorem を置き換えない。
policy file は実コードベース上の direct dependency evidence を数えるための tooling
入力であり、抽象射影の soundness / completeness は別の明示的な構造と theorem で扱う。

## extractor output への反映

policy file を適用した extractor output は、少なくとも `metricStatus` に測定根拠を残す。

```json
{
  "policies": {
    "policyId": "aatv2-local-policy",
    "schemaVersion": "signature-policy-v0",
    "boundaryGroupCount": 2,
    "abstractionRelationCount": 1
  },
  "signature": {
    "boundaryViolationCount": 1,
    "abstractionViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": true,
      "source": "policy:aatv2-local-policy"
    },
    "abstractionViolationCount": {
      "measured": true,
      "source": "policy:aatv2-local-policy"
    }
  },
  "policyViolations": [
    {
      "axis": "boundaryViolationCount",
      "source": "Formal.Arch.Patterns.RuntimeProtectionDesignPattern",
      "target": "Main",
      "sourceGroup": "formal-arch",
      "targetGroup": "entrypoint",
      "evidence": "import Main"
    }
  ]
}
```

policy が未指定の場合の規約は既存の `metricStatus` 方針を維持する。

```json
{
  "signature": {
    "boundaryViolationCount": 0,
    "abstractionViolationCount": 0
  },
  "metricStatus": {
    "boundaryViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    },
    "abstractionViolationCount": {
      "measured": false,
      "reason": "policy file not provided"
    }
  }
}
```

この placeholder 0 は Lean input 用の形を保つための値であり、empirical dataset では
欠損値として扱う。`deltaSignatureSigned` でも before / after のどちらかが
`measured = false` なら当該軸の delta は `null` にする。

## CLI contract

Sig0 / v1 extractor が policy file を読む場合の最小 CLI contract は次とする。

```bash
archsig --root . --policy signature-policy.json --out .lake/sig0.json
```

tooling 実装は、次を検査してから count を測定済みにする。

- `schemaVersion` が対応範囲内である。
- selector が測定対象 component id に対して解決できる。
- boundary group membership が local component ごとに一意である。
- abstraction relation の client / abstraction / implementation selector が空でない。
- unique dependency edge set を固定してから count している。

この検査に失敗した軸は `metricStatus.<axis>.measured = false` とし、理由を
`reason` に残す。実装が片方の policy だけを読める場合は、boundary と abstraction を
独立に `measured` / `not measured` として扱う。

## Lean との責務境界

policy schema は `ArchitectureSignature` の境界・抽象化軸を実コードベースへ接続する
tooling-side contract である。これは次を主張しない。

- extractor output が Lean の `ComponentUniverse` の完全な witness であること。
- selector coverage が現実コードベースの意味論を完全に表していること。
- boundary / abstraction violation count が単独で品質を決定すること。

Lean に渡す場合は、別途 finite component universe、coverage、edge closure、必要な
bridge theorem の前提を明示する。実証研究では `policyId`, extractor version,
rule set version, `metricStatus` を dataset に残し、policy の変更を交絡要因として扱う。
