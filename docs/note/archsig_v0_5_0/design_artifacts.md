> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計ノート — 出力 artifact 体系の再設計(CI 連携・ArchMap 連携)

設計次元 4 担当。調査ベース: reader_archsig-code / reader_archmap-lawpolicy / reader_saga / reader_ag-theory / reader_measurement-notes / reader_philosophy / reader_skills-workflow / reader_archview、および一次ファイル
`tools/archsig/src/schema/measurement.rs`、`tools/archsig/src/schema/constants.rs`、`tools/fieldsig/src/archmap.rs`。
査読 1 巡目(boundary 2 件 / theory 2 件 / feasibility 5 件 + major 2 件)反映済み。採否は文末「査読対応」節。

---

## 1. 目的

v0.5.0 の出力 artifact 体系を、次の 3 つの消費者に向けて再設計する。

1. **CI**: 機械可読な合否面(gate)と exit code。PR review では「変更が何を導入したか」の delta 読み。
2. **ArchMap authoring loop**: unmeasured / blocked な verdict が「次に何を観測すればよいか」という機械可読な観測要求になり、archmap-creater SKILL の complete-first ループを artifact で回せるようにする。
3. **FieldSig / ArchView**: measurement packet を唯一の handoff 源とし、行レベル assumption 依存と typed boundary を下流が読める形にする。

不変条件(全設計の前提):

- verdict 5 値(`measured_zero / measured_nonzero / unmeasured / unknown / not_computed`)を packet から exit code まで**どの層でも丸めない**(第VIII部 原則3.2)。
- packet は第VIII部 定義11.1 の 6 区画(profile / structuralVerdict / computedInvariants / analyticReadings / assumptions / nonConclusions)を保存・拡張する。
- 肯定的結論(`PASS_WITHIN_GATE_POLICY` 型)が全 surface の主役。boundary は typed で残すが主文にしない。
- 「比較可能性はデータである」(第X部 定理8.4/8.5)。計測間比較は comparison data を artifact として明示的に持ち回る。
- 結論相当フィールドを入力 schema に持たせない(anti-weakening、`research/goals/G-aat-quality-surface-06.md` material premise ledger)。

**出荷スコープ(v0.5.0 ゲート)**: 本文書は Phase A–E の設計を確定するが、**v0.5.0 の出荷ゲートは Phase A–C(命名統一 + packet v2 + gate)に限定する**。Phase D(delta / compare)は 0.5.x 追補、Phase E(frontier / viewer v3)は ArchView 再設計マイルストーンに切り出す(§5.1)。packet v2 は既存 `MeasurementProfileV1` の埋め込みで凍結し、LawPolicy 再設計次元の完了を待たない(§3.1)。

---

## 2. 現状の問題(調査で確定した事実)

### 2.1 schema 体系の不統一

- 表記が `x/v1`(slash)と `x-v1`(hyphen)で混在。キーも `schema` と `schemaVersion` が混在(`schema/constants.rs` 全体、viewer data は `schemaVersion: "archsig-atom-viewer-data-v2"`)。
- **run manifest が 3 様式**: v1 成功 = `"schemaVersion": "archsig-run-manifest-v1"`(cli/analyze.rs:36)、v2 成功 = `"schemaVersion": "archsig-run-manifest-v2"`(main.rs:847)、validation 失敗 = `"schema": "archsig-run-manifest/v1"`(main.rs:757)。キー名も値形式も不一致。
- insight-report / insight-brief は v2 分岐で常時出力されるが、manifest 契約として固定されていない。
- `Cargo.toml` の version が 0.1.0 のまま(README は v0.4.0 自称)。artifact に tool version が入らない。
- schema-catalog は v0 legacy 3 件を含む 21 artifact を列挙し、現行/廃止の region 区分が弱い。

### 2.2 packet v1 の残課題

v0.4.0 improvement PRD の R1(measured_zero 純度)/ R2(行レベル assumption 依存 `dependsOnAssumptions`)/ R3(`BoundaryStatementV1` 6 kind)/ R4(atom 語彙 lint)は**実装済み**(PR #2159/#2175/#2170/#2164)。真の残件は:

- **FieldSig が R2 を未採用**: `tools/fieldsig/src/archmap.rs:1046-` の assumptions 検証は「violated assumption が measured 行と併存したら packet-level contradiction」の保守 fail-fast のままで、`dependsOnAssumptions` を読まない。README の FieldSig 段落も「packet does not encode row-level assumption dependencies」と実装より古い。
- `computed_invariants: Vec<Value>` が untyped(schema/measurement.rs:13)。CI・FieldSig・viewer が invariant を機械的に参照できない。
- `dependsOnAssumptions` の参照先が assumption 行に安定 id を持たない(theoremRef + 文字列)。
- analytic reading に **certified / candidate の型区別が無い**(appendix B.1 が theorem candidate と分類する Wasserstein / stability / hotspot 等を出す場合の規律が schema に無い)。proxy(名称だけ理論先取り)のマーキングも schema 外。
- measured_zero 純度は empty_selected_scope ガード(ag_measurement.rs:6060-6073)で守られているが、**packet 上で機械検証できる形(scope サイズ・零を確立した計算への参照)になっていない**。
- 「concrete class, not merely nonzero group」(第IV部 原則4.4)の規律が schema 上に無い: verdict 行が「どの cover のどの class を測ったか」を構造化して指さない。

### 2.3 CI 連携の欠落

- 合否判定が `--strict-distance` フラグに畳み込まれ、しかも v1(distance 閾値)と v2(非終端 verdict / not_computed / violated assumption で exit 1)で**二義的**(main.rs:899-908)。「計測」と「制度的合否」が分離されていない。
- **pr-review コマンドは完全に v1 専用**(main.rs:575,612 の `ARCHMAP_V1_SCHEMA` 検査)。`archmap-delta-v0` は v1 atom id / molecule 語彙前提で、v2 の contexts / covers に対応する delta 型が存在しない(archmap_store.md も v0 語彙のまま)。
- 計測間比較(base vs head)の理論的裏付けが artifact に無い: 第X部 定理8.5(refinement 自然性はデータ)・第VIII部 定理7.3(refactor invariance は morphism データ要)に対応する supplied artifact が未定義。
- ArchMap の鮮度検証手段が無い(sources に revision / digest が無く、base ArchMap の stale 検出は SKILL の指示文のみ)。

### 2.4 ArchMap 連携の欠落

- complete-first ループ(coverage blocker を authoring 修理キューに変換)は archsig-reader SKILL の**散文読解**でしか回らない。unmeasured / blocked verdict から「次に必要な観測の形」を機械可読に出す artifact が無い。
- v0 で存在した observationGaps / confidence は v2 で(正しく)削除されたが、その結果「漏れの原因(見なかったのか・無かったのか)」を観測層に返す機械可読な回路が無い。

### 2.5 viewer data のドリフト

- `archsig-atom-viewer-data-v2` は v1 概念(moleculeGroups / atomEdges)と未採用機構(axisMapping / axisMetricBindings / 12-scene viewerVisualScenes)を emit し続け、一方で packet に実在する計測(locusField / periodStokes.meters / M2/M3/M5/M6 verdict 群 / transferCost)が ArchView に届いていない、または viewer contract で沈黙のまま。
- 「viewer は verdict を作らない」は nonClaims 文字列としては焼き込み済みだが、機械検証(viewer data 内の結論文字列が packet / summary に実在すること)が無い。

### 2.6 legacy artifact の残存

- v0 系(archsig-analysis-packet-v0、law-policy-v0、archmap-observation-map-v0 ほか)は CLI 不達のままコンパイル・catalog 掲載が続く。v1 系(typed-evaluator-results/v1、archsig-architecture-distance/v1、archsig-analysis-packet/v1、pr-review-report-v1)は破棄対象。FieldSig の `--analysis-packet`(v0/v1 受理)と足並みを揃える必要がある。

---

## 3. 設計案

### 3.0 artifact 体系の全体図

```
入力 artifact(observation / policy 層が author)
  archmap/v2                      … 既存(別次元で SKILL 強化)
  law-policy/v2                   … 別次元(LawPolicy 再設計)の成果物。本設計は interface のみ仮定
  archmap-delta/v1                … 新規(0.5.x)。PR の観測差分
  measurement-comparison/v1       … 新規(0.5.x)。計測間比較の supplied data(refinement / refactor morphism)
  archsig-gate-policy/v1          … 新規。verdict → CI 合否の制度的写像
  (gate-policy の authoring 責務は §3.2.1)

ArchSig 出力 artifact(machine 面)
  archsig-measurement-packet/v2   … 計測記録の正本(6 区画 + 拡張)
  archsig-run-manifest/v3         … 成功/失敗共通の単一様式
  archsig-gate-report/v1          … 新規。CI 合否面(exit code の根拠)
  archsig-comparison-report/v1    … 新規(0.5.x)。base/head の delta 読み
  archsig-observation-frontier/v1 … 新規(0.5.x)。ArchMap authoring への観測要求
  archmap-validation-report-v2 / law-policy-validation-report(既存系統)

ArchSig 出力 artifact(human 面)
  archsig-analysis-summary/v3     … conclusion-first の人間向け要約
  archsig-insight-report/v2 + archsig-insight-brief.md
  archsig-atom-viewer-data/v3     … ArchView 投影(packet の純射影、ArchView マイルストーン)

台帳
  schema-version-catalog/v1       … status(primary/deprecated)+ 消費者 + 置換関係
```

**命名規約(全 artifact 共通)**:

1. schema 識別子は必ず `"<artifact-name>/v<N>"` の slash 形式。hyphen 形式(`-v2`)は全廃。
2. トップレベルキーは必ず `"schema"`。`"schemaVersion"` キーは全廃。**経過措置**: viewer data のみ Phase E(v3 転換)までの間 `schemaVersion` キーの v2 のまま emit を続ける(ArchView を二度壊さないため。§5.1 Phase A)。
3. 全出力 artifact は次の共通ヘッダを持つ:

```json
{
  "schema": "archsig-measurement-packet/v2",
  "toolVersion": "0.5.0",
  "runId": "run:a1b2c3d4e5f6",
  "inputDigests": {
    "archmap": "sha256:…",
    "lawPolicy": "sha256:…",
    "profileFingerprint": "sha256:…"
  }
}
```

`inputDigests` は入力 JSON の正規化 digest(§3.0.1)。CI キャッシュと比較可能性判定(§3.3)の基盤になる。`Cargo.toml` を 0.5.0 に上げ、`toolVersion` は build 時に埋める。

### 3.0.1 digest / 決定論基盤(load-bearing な仕様)

digest は gate の `NOT_EVALUABLE` 判定、`delta-apply` の stale base 検出(exit 2)、comparability level(identical / verdict-row)の機械判定に直結する load-bearing な基盤なので、v0.5.0 で次を確定する。

1. **依存追加**: `sha2`(RustCrypto、pure Rust)を `tools/archsig/Cargo.toml` と `tools/fieldsig/Cargo.toml` に追加する。現行依存は両 crate とも clap / serde / serde_json / walkdir のみで、sha256 実装は存在しない。
2. **正規化アルゴリズム**: 入力 JSON を `serde_json::Value` に読み込み(object キーは serde_json 既定の BTreeMap 辞書順に正規化される)、空白・改行なしの compact 形式に再直列化した UTF-8 バイト列の SHA-256 とする。数値表現は serde_json の再直列化表現をそのまま採用する。**生バイト digest は採らない**(whitespace 整形差だけで stale / not-comparable に落ちるため)。RFC 8785 完全準拠は要求しない — digest の消費者は ArchSig 自身・FieldSig・CI のみで、外部実装との相互運用要件が無い。アルゴリズムは docs/tool の artifact 仕様に固定し、canonical fixture(既知入力 → 既知 digest)で lock する。
3. **siteCoverDigest の正規化対象**: normalized archmap のうち (a) `contexts` 区画、(b) `covers` 区画、(c) そこから導出される nerve 構造(選択 cover の chart 集合・重なり辺・三重交叉の incidence)のみを対象に、上記の正規化 digest を取る。`atoms` / `sources` の変更では変わらない。対象フィールドの列挙を schema docs に置き、fixture で lock する。
4. **runId の既定導出(決定的)**: `run:<sha256(archmapDigest ∥ lawPolicyDigest ∥ toolVersion) の先頭 12 hex>`。既定でタイムスタンプ・乱数を含まない(§3.9 の決定論規定と一体。同一入力 → 同一 runId → byte 同一出力)。`--stamp` を渡した場合のみ `run:<12hex>-<UTC時刻>` の suffix 付きになる(opt-in)。

### 3.1 measurement packet v2(`archsig-measurement-packet/v2`)

第VIII部 定義11.1 の 6 区画を保持したまま、行レベル依存・機械可読境界・measured_zero 純度・concrete class 規律・certified/candidate 分離・supplied/generated 台帳を焼き込む。

**profile 区画の凍結(v0.5.0 決定)**: packet v2 の `profile` は**既存 `MeasurementProfileV1` の解決済みコピーをそのまま埋め込み**、共通ヘッダの `profileFingerprint`(§3.0.1 の正規化 digest)を付す。LawPolicy 再設計次元が profile を将来 `measurement-profile/v2` として独立 artifact 化しても、packet 側は `profileFingerprint` の算出元が変わるだけで schema は変わらない。**packet v2 の出荷は LawPolicy 再設計の完了を待たない。**

```json
{
  "schema": "archsig-measurement-packet/v2",
  "packetId": "packet:…",
  "toolVersion": "0.5.0",
  "runId": "run:…",
  "inputDigests": { "archmap": "sha256:…", "lawPolicy": "sha256:…", "profileFingerprint": "sha256:…" },

  "profile": { "…": "解決済み MeasurementProfileV1 の埋め込みコピー(v1 と同一構造で凍結)" },

  "structuralVerdicts": [
    {
      "verdictId": "verdict:ag.cech-obstruction@1:law:no-hidden-coupling:cover:main",
      "evaluator": "ag.cech-obstruction@1",
      "law": "law:no-hidden-coupling",
      "target": {
        "kind": "cover-relative-cech-h1-class",
        "coverRef": "cover:main",
        "coefficient": "F2",
        "scopeSize": { "contexts": 4, "edges": 5, "triangles": 0 },
        "classRef": "invariant:cocycle-representative:cover:main"
      },
      "verdict": "measured_nonzero",
      "verdictData": {
        "inScope": true, "zero": false, "nonZero": true,
        "methodStatus": "ran", "certRef": "cert:…"
      },
      "dependsOnAssumptions": ["assumption:part8-4.2:finite-site:cover:main"],
      "evidence": {
        "computedInvariantRefs": ["invariant:cech-h1-rank:cover:main"],
        "sourceRefs": ["src:billing/service.rs:42"]
      },
      "reason": null
    }
  ],

  "computedInvariants": [
    {
      "invariantId": "invariant:cech-h1-rank:cover:main",
      "kind": "cech-h1-rank",
      "evaluator": "ag.cech-obstruction@1",
      "value": 1,
      "representation": {
        "cocycle": { "edge:left-bottom": 1, "edge:bottom-right": 0 },
        "coefficient": "F2"
      },
      "sourceRefs": ["src:…"]
    }
  ],

  "analyticReadings": [
    {
      "readingId": "reading:sheaf-laplacian:harmonic-mass:cover:main",
      "evaluator": "ag.sheaf-laplacian@1",
      "claimStatus": "certified",
      "fidelity": "proxy",
      "theoremRef": "part8/8.5",
      "value": { "harmonicMass": 0.42 },
      "regime": "graph-laplacian-hodge-proxy@1",
      "structuralVerdictRef": null
    },
    {
      "readingId": "reading:wasserstein-transfer-cost:…",
      "claimStatus": "candidate",
      "theoremRef": "part8/10.7(theorem candidate)",
      "…": "candidate は必ず theoremRef に candidate 出典を持つ"
    }
  ],

  "assumptions": [
    {
      "assumptionId": "assumption:part8-4.2:finite-site:cover:main",
      "theoremRef": "part8/4.2",
      "assumption": "finite poset site with finite selected cover",
      "status": "checked",
      "checkedBy": "archsig:site-finiteness-check",
      "scopeRefs": ["cover:main"]
    }
  ],

  "suppliedData": [
    {
      "suppliedId": "supplied:h1-comparison:identity:cover:main",
      "kind": "h1-comparison-data",
      "sourceArtifactRef": "measurement-comparison/v1:…",
      "conformance": {
        "checks": ["chart-map-total", "triple-map-total", "commutes-with-delta0", "residual-pullback-natural"],
        "status": "checked"
      }
    }
  ],

  "boundaryStatements": [
    {
      "id": "boundary:unmeasured-support:ctx:payments",
      "kind": "unmeasured_support",
      "scopeRefs": ["ctx:payments"],
      "reason": "selected cover does not include ctx:payments overlaps",
      "text": "…"
    }
  ],

  "nonConclusions": ["… boundaryStatements から導出される compat view(v1 同様)"]
}
```

v1 → v2 の変更点と根拠:

| 変更 | 内容 | 根拠 |
| --- | --- | --- |
| `structural_verdict` → `structuralVerdicts` + `verdictId` | 行に安定 id。gate / comparison / frontier / FieldSig が行参照できる | R2 の完成形(行レベル依存を下流が使うための前提) |
| `target` ブロック新設 | どの cover のどの class を測ったかを構造化(kind / coverRef / coefficient / classRef / scopeSize) | 第IV部 原則4.4(concrete class)。cover 相対性の明示 |
| `target.scopeSize` | 選択 scope の有限サイズを数値で焼き込み | **measured_zero 純度の機械検証**: packet validation が「`verdict == measured_zero` ⇒ `scopeSize` の該当成分 > 0 かつ `evidence.computedInvariantRefs` 非空」を invariant として検査。vacuous zero は schema 水準で排除される(R1 の artifact 化) |
| `evidence.computedInvariantRefs` | verdict と、それを確立した計算の双方向参照 | measured_zero / measured_nonzero が「どの計算に支えられたか」を機械可読化 |
| `computedInvariants` の typed 化 | `invariantId` + `kind`(registry で管理する閉語彙)+ `value` + `representation` | untyped `Vec<Value>` の解消。kind 初期語彙: `cech-h1-rank`, `cocycle-representative`, `cech-h2-rank`, `minimal-forbidden-supports`, `alexander-dual-hitting-sets`, `stanley-reisner-facets`, `tor1-class-support`, `boundary-residue-rank`, `nsdepth-certificate`, `nerve-b1`, `residual-boundary-membership`, `additive-h1-class`, `comparison-equivalence-witness`(末尾 3 つは SAGA 系の予約。§3.7) |
| `assumptions[].assumptionId` | 安定 id 化 | `dependsOnAssumptions` の参照先を id にし、FieldSig の行レベル propagation を可能にする(§3.5) |
| `analyticReadings[].claimStatus` | `certified` / `candidate` の 2 値 | appendix B.1 台帳(theorem candidate に依存する読みの型区別)。candidate 行は summary の headline に昇格禁止(validation で検査) |
| `analyticReadings[].fidelity` | `faithful` / `proxy` | 忠実性マップの measured_proxy(名称だけ理論先取り)を artifact 上で正直に宣言 |
| `suppliedData[]` 新設 | supplied な入力データ(comparison data / faithfulness data / incidence provenance 等)の台帳。ArchSig が検証した適合条件を記録 | 第X部の supplied/generated 規律の artifact 化。「結論は入力に格納されない」ことを、supplied 台帳 + 入力側 anti-weakening 検査(§3.3.4)の対で保証 |

**packet validation v2** は既存 `validate_measurement_packet_v1` を置換し、追加で次を検査する:

1. measured_zero 純度 invariant(上記)。
2. `dependsOnAssumptions` の全 id が `assumptions[].assumptionId` に解決する。violated assumption に依存する行が `not_computed` に正規化されている(既存 propagation の検査)。
3. `claimStatus: candidate` の reading が `structuralVerdictRef` を持たない(candidate を verdict の根拠にしない)。
4. verdict 行の `target.classRef` が `computedInvariants` に解決する(measured_nonzero の場合は必須 = concrete class 規律)。
5. boundaryStatements の kind が 6 値語彙内。

### 3.2 CI 連携 (1): 計測と合否の分離 — `archsig gate`

**設計原則: analyze は計測、gate は制度的判断。** 計測が走った以上 analyze は成功であり、verdict を exit code に直接埋め込まない。verdict → CI 合否の写像は組織の選択なので、明示的な policy artifact に外出しする。`--strict-distance` は廃止。

#### 3.2.1 `archsig-gate-policy/v1`(入力、CI 管理者が author)

```json
{
  "schema": "archsig-gate-policy/v1",
  "id": "gate-policy:main-branch",
  "rules": [
    {
      "gateId": "gate:no-h1-obstruction",
      "appliesTo": { "evaluators": ["ag.cech-obstruction@1"], "laws": ["law:no-hidden-coupling"] },
      "scope": "absolute",
      "onMeasuredZero": "pass",
      "onMeasuredNonzero": "block",
      "onUnmeasured": "pass_with_boundary",
      "onUnknown": "pass_with_boundary",
      "onNotComputed": "block",
      "onViolatedAssumptionDependency": "block"
    },
    {
      "gateId": "gate:no-new-obstruction-in-pr",
      "appliesTo": { "evaluators": ["ag.cech-obstruction@1", "ag.coherence-obstruction@1"] },
      "scope": "introduced-by-change",
      "onNewMeasuredNonzero": "block",
      "onClearedMeasuredNonzero": "pass",
      "onPreexistingMeasuredNonzero": "pass_with_boundary",
      "onRemovedVerdictRow": "pass_with_boundary",
      "onOtherTransition": "pass_with_boundary"
    }
  ]
}
```

規律:

- **fail-closed は scope 種別ごとに定義する**(機械検査可能な形で閉じる):
  - `scope: "absolute"` の rule は、verdict 5 値 + violated-assumption-dependency の **6 写像すべて**を明示必須。いずれかを省略した gate-policy は validation fail。
  - `scope: "introduced-by-change"` の rule は、comparison-report の `verdictTransitions` / `addedVerdictRows` / `removedVerdictRows` を機械分類した**閉じた 5 カテゴリ**への写像すべてを明示必須。分類規則(gate が機械適用):
    - `new_measured_nonzero` = 遷移先が `measured_nonzero`(遷移元 ≠ `measured_nonzero`)の transition、または `addedVerdictRows` の行で verdict が `measured_nonzero`
    - `cleared_measured_nonzero` = `measured_nonzero` → `measured_zero` の transition
    - `preexisting_measured_nonzero` = `measured_nonzero` → `measured_nonzero`
    - `removed_verdict_row` = `removedVerdictRows` の行
    - `other_transition` = 上記以外のすべて(unmeasured ↔ unknown 等の非終端間遷移、および non-nonzero の追加行)
- **非終端 verdict の plain pass 禁止(schema 制限)**: absolute rule の `onUnmeasured` / `onUnknown` / `onNotComputed` / `onViolatedAssumptionDependency`、および introduced-by-change rule の `onRemovedVerdictRow` / `onOtherTransition` の写像先は `pass_with_boundary` / `block` の **2 値に制限**する。plain `pass` を割り当てた gate-policy は validation fail。「unmeasured を黙って pass に丸める」は制度選択としても選べない(第VIII部 原則3.2 の丸め禁止 CI 版)。measured 系(`onMeasuredZero` / `onMeasuredNonzero` / `onNewMeasuredNonzero` / `onClearedMeasuredNonzero` / `onPreexistingMeasuredNonzero`)のみ 3 値全部を選べる。
- 写像語彙は `pass / pass_with_boundary / block` の 3 値のみ。`fail` という語を使わない(unknown は failure ではない、part_8:1099-1101)。`pass_with_boundary` は gate-report に typed boundary を残して通す。
- `scope: "introduced-by-change"` の rule は comparison-report(§3.3)を要求する。単独 run では `not_applicable` として skip(黙って pass にしない)。
- **authoring 責務**: gate-policy は CI 管理者(制度の選択者)が author する入力 artifact。v0.5.0 では専用 authoring SKILL を新設せず、保守的既定の starter テンプレート同梱 + docs/tool の gate-policy authoring ガイドで賄う。law-policy-creater の管轄には入れない(law の選択と CI 制度の選択を混ぜない)。SKILL 化は運用実績を見て判断する。

#### 3.2.2 `archsig-gate-report/v1`(出力、machine 合否面)

```json
{
  "schema": "archsig-gate-report/v1",
  "toolVersion": "0.5.0",
  "runId": "run:…",
  "gatePolicyRef": { "id": "gate-policy:main-branch", "digest": "sha256:…" },
  "packetRef": { "path": "archsig-measurement-packet.json", "digest": "sha256:…" },
  "comparisonRef": null,
  "decision": "PASS_WITHIN_GATE_POLICY",
  "ruleOutcomes": [
    {
      "gateId": "gate:no-h1-obstruction",
      "outcome": "pass",
      "verdictRefs": ["verdict:ag.cech-obstruction@1:law:no-hidden-coupling:cover:main"],
      "appliedMapping": { "verdict": "measured_zero", "action": "pass" }
    }
  ],
  "boundary": [
    { "kind": "unmeasured_support", "gateId": "…", "verdictRefs": ["…"], "text": "passed with boundary: unmeasured is not zero" }
  ],
  "headline": "PASS_WITHIN_GATE_POLICY: 2 gates evaluated, 0 blocking, 1 passed with boundary"
}
```

- `decision` は `PASS_WITHIN_GATE_POLICY` / `BLOCKED_BY_GATE_POLICY` / `NOT_EVALUABLE`(packet 不在・digest 不一致等)の 3 値。
- `appliedMapping` に「どの verdict がどの規則でどう写像されたか」を全行記録する。**丸めの痕跡が常に残る**ので、後から「なぜ通ったか / 止まったか」を verdict 語彙のまま監査できる。非終端 verdict は §3.2.1 の schema 制限により必ず `pass_with_boundary` か `block` に落ちるため、boundary 区画にも typed で必ず現れる。

#### 3.2.3 exit code 体系

| コマンド | 0 | 1 | 2 | 3 |
| --- | --- | --- | --- | --- |
| `archsig analyze` | 計測完了(verdict の内容に関わらず) | — | 入力 contract 違反(validation 失敗。失敗 artifact + manifest は emit) | 内部エラー |
| `archsig gate` | `PASS_WITHIN_GATE_POLICY` | `BLOCKED_BY_GATE_POLICY` | 入力不正(policy 不正 / packet 不在 / digest 不一致) | 内部エラー |
| `archsig compare` | 比較レポート生成 | — | 入力不正 | 内部エラー |
| `archsig delta-apply` | 適用完了 | — | 入力不正 / stale base(digest 不一致) | 内部エラー |

exit code に verdict は直接現れない。CI の分岐は必ず gate-report(とその appliedMapping)を経由する。

#### 3.2.4 CLI 例(CI での標準列)

```bash
# main ブランチ(絶対 gate のみ)
archsig analyze --archmap archmap.json --law-policy law_policy.json --out-dir .tmp/run
archsig gate --run-dir .tmp/run --gate-policy gate_policy.json \
             --out .tmp/run/archsig-gate-report.json
# exit code 0/1 が CI の合否
```

`--run-dir` は run manifest から packet を解決する。単発 packet を直接渡す `--packet` も可。

### 3.3 CI 連携 (2): PR review の delta 読み — `archmap-delta/v1` + `archsig compare`(0.5.x)

v1 専用 `pr-review` コマンドと `archmap-delta-v0` は廃止し、v2 語彙の delta と比較レポートに置き換える。本節の実装は Phase D(0.5.x 追補)。v0.5.0 時点では pr-review を deprecated として告知のみ行う(§5.1)。

#### 3.3.1 `archmap-delta/v1`(入力、観測層が author)

```json
{
  "schema": "archmap-delta/v1",
  "id": "delta:pr-1234",
  "base": { "archmapId": "archmap:shop-service", "contentDigest": "sha256:…" },
  "provenance": {
    "sourceKind": "git-pr",
    "gitBase": "b3430c12…", "gitHead": "9f2e…", "prRef": "org/repo#1234"
  },
  "changes": {
    "sources": [ { "op": "add", "key": "src:billing/refund.rs", "value": { "kind": "file", "path": "billing/refund.rs" } } ],
    "atoms":   [ { "op": "add", "atom": { "id": "atom:refund-emits-event", "kind": "effect", "…": "archmap/v2 atom そのまま" } },
                 { "op": "replace", "id": "atom:order-section-left", "atom": { "…": "…" } },
                 { "op": "remove", "id": "atom:legacy-hook" } ],
    "contexts": [ { "op": "replace", "id": "ctx:billing", "context": { "…": "…" } } ],
    "covers":   [ ]
  },
  "comparison": { "ref": "measurement_comparison.json" },
  "nonConclusions": ["delta records observation changes only; it asserts no measurement conclusion"]
}
```

- `changes` は archmap/v2 の 4 区画(sources / atoms / contexts / covers)にちょうど対応する。molecule 語彙は存在しない。
- **base digest 検査**: `archsig delta-apply` は `base.contentDigest`(§3.0.1 の正規化 digest)と手元の base archmap の digest 一致を検査し、不一致は exit 2(stale base の機械検出。skills レポート §4.5 の鮮度ギャップへの回答)。
- delta の中身にも archmap/v2 と同一の検証(diagnostic-shortcut 拒否・語彙検査・refs 解決)が適用される。**観測純化の規律は delta 経由でも破れない**。
- `comparison` は任意。contexts / covers を変更する delta が計測間の class 水準比較を望む場合にだけ、`measurement-comparison/v1` を添える(§3.3.3)。

#### 3.3.2 `archsig compare` と `archsig-comparison-report/v1`

```bash
# PR CI の標準列(0.5.x)
archsig delta-apply --base archmap.base.json --delta pr.archmap-delta.json \
                    --out archmap.head.json
archsig analyze --archmap archmap.base.json --law-policy law_policy.json --out-dir .tmp/base
archsig analyze --archmap archmap.head.json --law-policy law_policy.json --out-dir .tmp/head
archsig compare --base-run .tmp/base --head-run .tmp/head \
                [--comparison measurement_comparison.json] \
                --out .tmp/archsig-comparison-report.json
archsig gate --run-dir .tmp/head --comparison .tmp/archsig-comparison-report.json \
             --gate-policy gate_policy.json --out .tmp/archsig-gate-report.json
```

```json
{
  "schema": "archsig-comparison-report/v1",
  "toolVersion": "0.5.0",
  "base": { "runId": "…", "packetDigest": "sha256:…", "archmapDigest": "sha256:…",
            "profileFingerprint": "sha256:…", "siteCoverDigest": "sha256:…" },
  "head": { "…": "同形" },
  "comparability": {
    "level": "verdict-row",
    "basis": "identical-profile-and-site-cover",
    "comparisonDataRef": null
  },
  "transport": null,
  "conclusionCode": "MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE",
  "verdictTransitions": [
    {
      "verdictId": "verdict:ag.cech-obstruction@1:law:no-hidden-coupling:cover:main",
      "from": "measured_zero", "to": "measured_nonzero",
      "transition": "obstruction-after-zero",
      "deltaRefs": ["atom:order-section-left"]
    }
  ],
  "addedVerdictRows": [], "removedVerdictRows": [],
  "boundary": [
    { "kind": "not_comparable_without_comparison_data",
      "scopeRefs": ["cover:main→cover:main-refined"],
      "text": "cover structure changed; class-level transport requires measurement-comparison/v1" }
  ],
  "discipline": [
    "verdict transitions are records of verdict rows for the same target under identical profile and site cover; they assert no class identity and no transport",
    "deltaRefs list mechanically overlapping delta operations; they assert no causal attribution"
  ]
}
```

**比較可能性の 3 段階(理論に接地した中核設計)**:

| level | 成立条件(機械判定) | 語れること | 理論根拠 |
| --- | --- | --- | --- |
| `identical` | `archmapDigest` と `profileFingerprint` が一致 | 同一計測。transition なし | 自明 |
| `verdict-row` | `profileFingerprint` 一致 **かつ** `siteCoverDigest`(§3.0.1)一致 | 同名 target(同一 cover の同一 class 名)の verdict 行を記録として並置し、transition をラベルする(`obstruction-after-zero` / `zero-after-obstruction` — ArchView sequence mode と同語彙)。**class の同一性・transport は主張しない** | 同一の測定対象族に対する 2 回の独立計測の記録差分。補間・新 verdict 生成をしない規律は ArchView sequence mode で確立済み |
| `class-transport` | `measurement-comparison/v1` が供給され、kind ごとの適合条件検査(§3.3.3)に合格 | **kind ごとの licensed conclusion 形(下表)のみ** | 第X部 命題4.10(粗→細の片方向)・定理8.5(逆方向は反例で遮断)、第VIII部 定義7.2 / 定理7.3 |

**class-transport の kind 別 license(理論が許す形に限定)**:

| kind | 方向 | licensed conclusion 形 | 遮断される形(typed boundary として沈黙) |
| --- | --- | --- | --- |
| `identity` | 双方向 | 両 run の verdict 行の同一視(digest から自動導出) | — |
| `refinement` | **base(粗)→ head(細)の片方向のみ** | 粗 cover 側の境界所属・H¹-zero の細 cover 側への保存(第X部 命題4.10) | 細→粗方向の zero 転送。第X部 定理8.5 の反例(coarse-zero / fine-nonzero、Lean: `refinementZeroComparison_not_unconditional_for_coarseZero_fineNonzero`)が追加データなしの逆方向を明示的に遮断する |
| `refactor-morphism` | 射の向きの pullback reading のみ | 第VIII部 定義7.2 の pullback reading。**zero iff(双方向対応)は `equivalenceData`(定理7.3 の仮定: selected finite site equivalence + ringed ambient / 係数 / law ideal の同型)が supplied かつ conformance 検査合格の場合のみ** | equivalenceData 無しの双方向 class 対応・zero iff |

comparison-report は class-transport 水準では `transport` 区画を埋める:

```json
"transport": {
  "kind": "refinement",
  "direction": "base-to-head",
  "licensedConclusions": ["coarse-boundary-membership-preserved", "h1-zero-preserved-under-refinement"],
  "comparisonDataRef": "measurement_comparison.json",
  "conformance": { "status": "checked",
                   "checks": ["chart-map-total", "triple-map-total", "commutes-with-delta0", "residual-pullback-natural"] }
}
```

**validation(逆方向遮断の機械化)**: `transport.direction` が kind の licensed 方向と一致しない comparison-report、および `licensedConclusions` に kind の license 外の結論形を含む comparison-report は validation fail。`kind: refinement` で head→base 方向の zero 転送を実装しても artifact contract 違反として止まる。

**comparability level → 発行可能 conclusionCode の対応表**:

| level | 発行可能な conclusionCode |
| --- | --- |
| `identical` | `NO_NEW_MEASURED_OBSTRUCTION_RECORDED` のみ(transition は定義上生じない) |
| `verdict-row` | `NO_NEW_MEASURED_OBSTRUCTION_RECORDED` / `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE` / `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` |
| `class-transport` | 上記に加え `ZERO_PRESERVED_UNDER_REFINEMENT`(refinement、base→head のみ)/ `VERDICTS_CORRESPOND_UNDER_SITE_EQUIVALENCE`(refactor-morphism、equivalenceData 検査合格時のみ) |
| (不成立) | `RUNS_NOT_COMPARABLE_WITHOUT_COMPARISON_DATA` |

**claim 形の固定(規範)**: `MEASURED_OBSTRUCTION_RECORDED_AFTER_CHANGE` / `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` は「同一 `profileFingerprint` + `siteCoverDigest` 下の同名 target に対する verdict **記録**の遷移」であり、class の同一性・transport(「同じ障害が残っている / 直った」)を主張しない。この claim 形は上記 `discipline` 文字列として artifact に焼き込み、fixture で lock する。旧称候補の `…_INTRODUCED_BY_CHANGE` / `…_CLEARED_BY_CHANGE` は因果・transport 読みを誘発するため採用しない。site / cover が変わったのに comparison data が無い場合、compare は**両 run の独立な結論を並置し、typed boundary を 1 行置いて沈黙する**。transport 主張は class-transport 水準の licensed conclusion としてのみ、供給・検査済みデータの下で発行される。

**deltaRefs の機械的導出規則**: `verdictTransitions[].deltaRefs` は「delta の `changes` に列挙された op の対象 id 集合(atoms / contexts / covers / sources)」と「当該 verdict 行が参照する id 集合(`target.coverRef` とその cover の構成 contexts、`evidence.sourceRefs`、依存 assumption の `scopeRefs`)」の**機械的交差**である。交差が空なら `[]`(省略しない)。これは併記(overlap listing)であって因果帰属ではない — この旨も `discipline` に焼き込む。gate の introduced-by-change 分類(§3.2.1)は from/to と added/removed だけを使い、deltaRefs に依存しない。

#### 3.3.3 `measurement-comparison/v1`(入力、supplied data)

```json
{
  "schema": "measurement-comparison/v1",
  "id": "comparison:pr-1234",
  "kind": "refinement",
  "baseCoverRef": "cover:main",
  "headCoverRef": "cover:main-refined",
  "chartMap": [
    { "base": "ctx:billing", "head": ["ctx:billing-core", "ctx:billing-adapter"] }
  ],
  "edgeMap": [ { "base": "edge:billing~checkout", "head": ["edge:billing-core~checkout"] } ],
  "tripleMap": [ { "base": "tri:billing~checkout~payments", "head": ["tri:billing-core~checkout~payments"] } ],
  "nonConclusions": ["comparison data supplies mappings only; it stores no quotient equality, no zero class, no descent conclusion"]
}
```

- `kind`: `identity`(自動導出可、level 2 と等価)/ `refinement`(粗→細)/ `refactor-morphism`(site 射 + 互換データ)。
- **kind ごとの必須データと適合条件(確定)**:
  - `identity`: 追加データ不要。digest 一致から自動導出。
  - `refinement`: `chartMap` / `edgeMap` / **`tripleMap`(三重交叉の写像)** を必須とする。適合条件 = `chart-map-total`(選択 cover の全 chart を写す全域性)/ `triple-map-total` / `commutes-with-delta0`(δ⁰ との可換性: 写像に沿った制限が両側で一致)/ `residual-pullback-natural`(residual への引き戻しの自然性)。これは第X部 命題4.10 が refinement data として要求する形をそのまま schema 化したもので、tripleMap と δ⁰・residual 自然性を欠く供給データでは class-transport 水準に到達しない。
  - `refactor-morphism`: `siteMorphism`(chart / edge / triple 対応)を必須とする。pullback reading(定義7.2)はこれだけで licensed。**zero iff を望む場合のみ** `equivalenceData`(site equivalence の逆向きデータ + ringed ambient / 係数 / law ideal の同型)を追加供給し、第VIII部 定理7.3 の仮定を conformance checks として検査する。
- **anti-weakening 検査**: comparison / delta / 将来の faithfulness 系入力 artifact に対し、archmap/v2 の diagnostic-shortcut 検査と同系の**結論語彙 hard error**を適用する(`h1Zero`, `coherent`, `glues`, `equivalent` 等の結論相当フィールド名・値を入力に見つけたら fail)。第X部 定義7.1「comparison data は結論を格納しない」の実装形。
- ArchSig は supplied comparison の適合条件(上記 kind 別)を検査してから transport を計算し、検査結果を packet の `suppliedData[].conformance` と comparison-report の `transport.conformance` に記録する。

#### 3.3.4 ArchMapStore との関係

v0.5.0 スコープは **delta のみ**。`archmap_store.md` の commit / snapshot / index は v0 語彙のまま設計文書として残るが、「delta は archmap-delta/v1 に置換済み、他は未実装構想」と同文書に注記して三世代ドリフトを止める。store 本体(履歴・圧縮)は FieldSig の longitudinal 責務と重なるため、v0.5.0 では判断を保留する(§6)。

### 3.4 ArchMap 連携: `archsig-observation-frontier/v1`(観測要求の機械可読化、0.5.x)

**問い**: unmeasured / blocked verdict を「次の観測要求」に変換する循環を、観測純化と沈黙の規律を壊さずに作れるか。

**答えの骨子**: frontier は**診断結論の一部ではなく、authoring 層に宛てた作業 artifact** である。archmap-creater SKILL に既にある complete-first ループ(coverage blocker を authoring 修理キューへ変換し、user handoff 前に消化する)の散文部分を機械可読化するだけであり、新しい主張は導入しない。

```json
{
  "schema": "archsig-observation-frontier/v1",
  "toolVersion": "0.5.0",
  "runId": "run:…",
  "packetRef": { "path": "archsig-measurement-packet.json", "digest": "sha256:…" },
  "profileRef": "profile:shop-default",
  "entries": [
    {
      "frontierId": "frontier:ag.boundary-residue@1:unmeasured-support:ctx:payments",
      "drivenBy": {
        "verdictRef": "verdict:ag.boundary-residue@1:law:boundary-locality:cover:main",
        "boundaryStatementRef": "boundary:unmeasured-support:ctx:payments"
      },
      "requestKind": "unmeasured_support",
      "neededObservation": {
        "atomKind": "semantic",
        "axis": "cech",
        "predicate": "sectionValue",
        "forContexts": ["ctx:payments", "ctx:checkout"],
        "note": "boundary residue over cover:main needs raw section values on the payments/checkout overlap"
      }
    }
  ],
  "discipline": [
    "entries are observation requests within the selected profile scope",
    "entries are not measurement conclusions and not completeness obligations",
    "an entry asks for raw observations (values, supports, restriction edges) only; it never asks for judgements or computed results",
    "entries carry no disposition; classifying a request as private, unavailable, or out of scope is an authoring-layer judgement outside this artifact"
  ]
}
```

生成規則(規律の中核):

1. **導出源の限定**: entry は (a) `verdict ∈ {unmeasured, unknown, not_computed}` かつ `verdictData.inScope == true` の行、(b) boundaryStatements のうち kind ∈ `{unmeasured_support, blocked_method, violated_assumption}` からのみ導出する。**`silence_by_design` と `out_of_selected_vocabulary` からは entry を作らない** — 語彙の外は沈黙のまま。語彙拡大の要求を tool が生成しない(それは LawPolicy / ユーザーの決定)。
2. **要求の形の限定**: `neededObservation` は archmap/v2 が書ける生観測の形(atomKind / axis / predicate / contexts / covers の形状)だけを指定する。値・判定・計算結果は一切要求しない。observation purity(charter 原則1-2)を要求側でも保つ。
3. **有限性**: entry は選択された evaluator × 選択された law × 選択された cover の要求と、供給された atoms の差から機械的に決まる有限リスト。extraction completeness への言及は schema 上存在しない(`discipline` に非義務を明記)。
4. **分類の非所有(disposition を持たない)**: entry に disposition(repairable / private / unavailable / out-of-scope 等)の分類フィールドを**持たせない**。観測可能性の判別(private か・unavailable か・out-of-scope か)は入力 contract の外にある世界知識であり、ArchSig が生成時に埋めると「入力 contract を補完・推測しない」規律に抵触する。分類は archmap-creater SKILL の作業台帳(authoring 層)が所有し、law_policy.md の residual gap 規律(private / unavailable / out-of-scope のみが正当な残差)に従って author が記入する。なお全 entry は規則 2 により定義上 archmap/v2 で表現可能な要求形なので、「表現可能か」の機械判定フィールドも不要である。
5. **配置**: frontier は run manifest の `artifacts.authoring` 区画に置かれ、summary / insight brief の headline には現れない(件数のみ metadata 行)。診断面の主役は常に肯定的結論。

循環の全体像:

```
archsig analyze → packet + frontier
      ↓ (archmap-creater SKILL が frontier を読み、生観測を追記)
archmap v2 (revised)
      ↓
archsig analyze → frontier が縮む(観測が供給された entry が消える)
      ↓
残った entry は SKILL 側の作業台帳で author が private / unavailable / out-of-scope に分類し、
ユーザーに引き継ぐ(law_policy.md の residual gap 規律。分類は authoring 層の判断であり、
frontier artifact には現れない)
```

### 3.5 FieldSig handoff v2

現状: FieldSig は `archsig-measurement-packet/v1` を受理済み(fieldsig/src/archmap.rs:277-)だが、(a) `dependsOnAssumptions` を読まず violated assumption と measured 行の併存を packet-level contradiction として fail-fast(同 :1046-)、(b) v0 `archsig-analysis-packet-v0` / v1 raw packet の受理コードが残存。

v0.5.0 の handoff 契約:

1. FieldSig は `archsig-measurement-packet/v2` を受理する。**行レベル propagation 採用**: violated assumption は、`dependsOnAssumptions` でそれに依存する行だけを影響範囲として扱い、無関係な measured 行は取り込む。packet-level fail-fast は「violated assumption に依存する行が measured のまま残っている packet」(= packet validation v2 違反)にのみ発動する。
2. boundaryStatements を typed のまま SFT input の measurement_boundary_refs へ写す(現状の non_conclusions 文字列読みを置換)。
3. v0 analysis-packet / v1 raw packet / v1 measurement packet の受理コードは、ArchSig 側の v1 emit 停止と同一 PR 系列(Phase B)で削除する。
4. **移行窓は置かない(atomic 切替)**: fieldsig は release asset として配布されておらず(archsig-release.yml の配布物は archsig バイナリのみ、4 platform)、packet の消費者は monorepo 内(FieldSig / ArchView / SKILL / CI)に閉じている。v1/v2 両受理窓・dual-emit は受益者が存在しないため設けない(§5.2 のリスク行参照)。

```bash
fieldsig archsig-analysis-sft-input \
  --measurement-packet .tmp/run/archsig-measurement-packet.json \
  --out .tmp/fieldsig/operation-support-estimate.json
```

### 3.6 viewer data の位置づけ: `archsig-atom-viewer-data/v3`(ArchView マイルストーン)

viewer data は「packet + normalized archmap の**純射影**」という位置づけを schema で固定する。**本節は artifact 契約の確定のみを本設計で行い、v3 の実装・出荷は ArchView 再設計(次元 6)のマイルストーン(0.5.x、§5.1 Phase E)と同期する。** v0.5.0 の間、viewer data は現行 v2(`schemaVersion` キー)のまま emit を続ける(命名統一の唯一の例外。二度の breaking 変更で ArchView を二度壊さないため)。

1. **schema 統一**: キー `schema`、値 `archsig-atom-viewer-data/v3`(v3 転換時に一括)。
2. **v1 語彙の削除**: `moleculeGroups` / `atomEdges`(v1 概念、ArchView 未使用)を削除。`viewerVisualScenes` の 12-scene 語彙・`axisMapping` / `axisMetricBindings` は、次元 6 の決定に従い「`sceneAvailability[]`(sceneId / active / drivenBy)」へ置換する。
3. **drivenBy 規律の機械化**: すべての幾何要素(nerve edge / seam / cage / meter / membrane…)は `drivenBy` フィールドで packet 内の `verdictId` / `invariantId` / `readingId` を指す。**packet に対応物の無い幾何要素は viewer data validation で fail**。「計測=主・可視化=従」の捏造防止を、nonClaims 文字列から実行可能検査に昇格する。
4. **結論文字列の照合検査**: viewer data 内の conclusion / verdict 文字列は summary / packet に実在するものに限る(新 verdict 生成の機械的禁止、guideline.md:14/36 の実装形)。
5. **既測・未投影の解消**: packet v2 に存在する H² verdict、boundary-residue / restriction-compatibility / section-factorization の verdict 参照、locusField、periodStokes.meters、transferCost を v3 の投影対象として保持・整理する(描くかどうかは ArchView 側の決定。artifact は運ぶ)。SAGA 系(§3.7)の `sagaGeometry` 区画(charts / overlaps / residual class support / repair support)を予約する。
6. ArchView の sibling fetch 契約(`./archsig-atom-viewer-data.json` ほか)と `archview-sequence/v1` は維持。sequence mode の「frame = 独立な実測 packet、transition はラベルのみ」の規律は comparison-report(§3.3.2)の transition 語彙と共通化する。

### 3.7 SAGA / 新 evaluator の受け皿(artifact 側の予約)

evaluator 群の設計は AG 分析次元の担当だが、artifact 体系は次を予約する:

- `computedInvariants.kind` に `residual-boundary-membership`(r ∈ B¹ の生値)、`additive-h1-class`、`comparison-equivalence-witness` を予約(§3.1)。
- SAGA の入力 5 層(semantic projection / 有限複体 / additive 係数 + faithfulness / 比較 / law-equation)のうち supplied なものは、archmap/v2 拡張または独立入力 artifact として次元 2(ArchMap)・次元 3(LawPolicy)が設計する。**packet 側は `suppliedData[]` 台帳と適合条件検査の枠だけを持ち、どの層まで供給されたかに応じた結論の階段**(生値 → 無条件の否定的診断 → faithfulness 下の肯定的 descent → class 転送 → law-grounded 結論)を verdict 行の `target.kind` と `dependsOnAssumptions` で表現する。
- summary の conclusionCode に `REPAIR_GLUES_UNDER_PROFILE` / `MEASURED_REPAIR_GLUING_OBSTRUCTION_UNDER_PROFILE` を予約。complete-support regime(第X部 定理3.5)で faithfulness 供給不要の肯定的結論が出せる最初の入口になる。

### 3.8 human 面: `archsig-analysis-summary/v3` と insight brief

- summary v3 は conclusion-first を維持: `conclusionCode`(閉語彙 registry: `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `MEASURED_AG_OBSTRUCTION_UNDER_PROFILE` / `AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE` / `VALIDATION_FAILED_BEFORE_MEASUREMENT` + §3.7 予約)+ `readThisFirst` + `verdictDigest`(5 値の件数)+ `topFindings[]`(肯定的結論先頭)+ `boundaryDigest`(短文)+ `artifactLinks`。
- conclusionCode registry は Rust の const + schema-catalog エントリ + fixture lock の三点で固定し、summary 文言とのドリフトを防ぐ。
- insight report / brief は human 面として存続(v2 に bump、frontier 件数を metadata 行として持つが headline にしない)。
- **PR コメント生成は ArchSig 本体の責務にしない**。archsig-pr-reviewer SKILL の v2 後継が comparison-report + gate-report を読んで人間語へ翻訳する(machine 面 / human 面の分離を製品面でも維持)。

### 3.9 run manifest v3(単一様式)と出力ディレクトリ

```json
{
  "schema": "archsig-run-manifest/v3",
  "toolVersion": "0.5.0",
  "runId": "run:…",
  "mode": "measurement",
  "inputDigests": { "archmap": "sha256:…", "lawPolicy": "sha256:…", "profileFingerprint": "sha256:…" },
  "conclusionCode": "NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE",
  "artifacts": {
    "machine": {
      "measurementPacket": "archsig-measurement-packet.json",
      "archmapValidation": "archmap-validation.json",
      "lawPolicyValidation": "law-policy-validation.json",
      "normalizedArchmap": "normalized-archmap.json",
      "packetValidation": "archsig-packet-validation.json"
    },
    "human": {
      "summary": "archsig-analysis-summary.json",
      "insightReport": "archsig-insight-report.json",
      "insightBrief": "archsig-insight-brief.md",
      "viewerData": "archsig-atom-viewer-data.json"
    },
    "authoring": {
      "observationFrontier": "archsig-observation-frontier.json"
    }
  }
}
```

- **成功・失敗で同一 schema**。`mode: "validation-failure"` の場合は `artifacts.machine.validation*` と失敗 insight のみが埋まり、`conclusionCode: "VALIDATION_FAILED_BEFORE_MEASUREMENT"`。3 様式問題を解消する。
- 決定論: 出力は既定でタイムスタンプ・乱数を含まない(golden test / CI キャッシュのため)。runId は入力 digest からの決定的導出(§3.0.1)。`--stamp` で runId に時刻を含める opt-in。
- gate-report / comparison-report は analyze の出力ではないので manifest 外(それぞれのコマンドが独立 artifact として出力し、互いに digest で参照する)。

### 3.10 versioning / schema catalog 方針

**catalog v1**(`schema-version-catalog/v1`、slash 形式へ bump):

```json
{
  "schema": "schema-version-catalog/v1",
  "toolVersion": "0.5.0",
  "artifacts": [
    {
      "name": "archsig-measurement-packet", "version": "v2", "status": "primary",
      "direction": "output", "producedBy": ["archsig analyze"],
      "consumers": ["fieldsig", "archview", "archsig gate", "archsig compare", "skills"],
      "replaces": "archsig-measurement-packet/v1"
    },
    {
      "name": "archsig-measurement-packet", "version": "v1", "status": "deprecated",
      "removal": "0.6.0", "note": "not emitted since 0.5.0 (single cut-over, see release notes); catalog entry documents the replaces relation"
    }
  ]
}
```

方針(規範):

1. **1 artifact = 1 名前 + slash 版数、`schema` キー**。改名・キー変更・意味変更は版数 bump とし、catalog に `replaces` を記録する。
2. **入力は fail-closed、出力は additive-tolerant**: 入力 schema は `deny_unknown_fields` を維持。出力 schema への互換的フィールド追加は版数据え置きで許し、消費者(FieldSig / ArchView / SKILL)は未知フィールドを無視する義務を負う(catalog に明記)。
3. **全 artifact に `toolVersion` + `inputDigests`**。同一入力 digest → 同一出力(決定論)を CI の再現性検査に使う。
4. catalog は `archsig schema-catalog` の出力 + canonical fixture で lock。v0 legacy エントリは catalog から削除し、v1 系は `deprecated(removal: 0.6.0)` として 1 release 掲載する(**告知のみ。dual-emit はしない**。切替は v0.5.0 の単一 breaking cut-over であり、消費者は monorepo 内で atomic に追随する)。
5. **命名移行表**(v0.5.0 で確定、出荷 Phase を併記):

| 現行 | v0.5.0 系 | Phase / 備考 |
| --- | --- | --- |
| `archsig-measurement-packet/v1` | `archsig-measurement-packet/v2` | B(v0.5.0)。§3.1。単一切替、dual-emit なし |
| `archsig-analysis-summary/v2` | `archsig-analysis-summary/v3` | B(v0.5.0)。conclusionCode registry 化 |
| `archsig-insight-report/v1` | `archsig-insight-report/v2` | B(v0.5.0)。frontier 参照追加は E で |
| `archsig-atom-viewer-data-v2`(schemaVersion キー) | `archsig-atom-viewer-data/v3`(schema キー) | E(0.5.x、ArchView 同期)。それまで v2 のまま(§3.6) |
| `archsig-run-manifest-v1` / `-v2` / `…/v1` 混在 | `archsig-run-manifest/v3` | A(v0.5.0)。単一様式 |
| `archmap-delta-v0` | `archmap-delta/v1` | D(0.5.x)。v2 語彙 |
| `archsig-pr-review-report-v1` | `archsig-comparison-report/v1`(+ gate-report) | D(0.5.x)。v0.5.0 では pr-review を deprecated 告知 |
| (新規) | `archsig-gate-policy/v1`, `archsig-gate-report/v1` | C(v0.5.0) |
| (新規) | `measurement-comparison/v1`, `archsig-observation-frontier/v1` | D / E(0.5.x) |
| 削除 | `archsig-analysis-packet-v0/v1`, `typed-evaluator-results/v1`, `archsig-architecture-distance/v1`, `law-policy-v0`, `archmap-observation-map-v0`, viewer/manifest の v0/v1 | A–B(emit 側)、F(dead コード) |

### 3.11 CI ワークフロー(lean.yml e2e)の新形

リポジトリに root Cargo.toml(workspace)は存在しないため、現行 lean.yml と同じ `--manifest-path` 形式を使う。**workspace 化は本設計のスコープ外**(採るなら `.lake` / CI キャッシュへの影響確認を伴う独立 Issue とし、暗黙に混ぜない)。

```yaml
# push (main): 絶対 gate(v0.5.0 出荷ゲート内)
- run: cargo run --manifest-path tools/archsig/Cargo.toml -- analyze --archmap fx/archmap.json --law-policy fx/law_policy.json --out-dir .tmp/e2e
- run: cargo run --manifest-path tools/archsig/Cargo.toml -- gate --run-dir .tmp/e2e --gate-policy fx/gate_policy.json --out .tmp/e2e/gate.json
- run: cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input --measurement-packet .tmp/e2e/archsig-measurement-packet.json --out .tmp/e2e/sft-input.json
- run: cargo run --manifest-path tools/archsig/Cargo.toml -- schema-catalog --out .tmp/e2e/catalog.json && diff .tmp/e2e/catalog.json fx/schema_version_catalog.json

# pull_request: delta gate(0.5.x、Phase D で導入)
- run: cargo run --manifest-path tools/archsig/Cargo.toml -- delta-apply --base fx/archmap.base.json --delta fx/pr.delta.json --out .tmp/head.json
- run: … analyze base / analyze head / compare / gate --comparison …
```

v1 前提だった e2e 前半(lean.yml:49-201)は、v0.5.0 では push 側(analyze + gate + fieldsig + catalog)の形へ置換し、pull_request 側の delta gate は Phase D で追加する。golden corpus には「同一入力 digest → byte 同一出力」の決定論 lock(§3.0.1)を追加する。

---

## 4. 境界規律との整合

philosophy レポートのチェックリスト(C/D 系)への対応を明示する。

| 規律 | 本設計での実装 |
| --- | --- |
| D1 5 値保存 | packet → gate-report(appliedMapping)→ comparison-report(transition の from/to)→ FieldSig(行レベル)まで 5 値語彙のまま流れる。どの層にも縮約語彙(pass/fail の 2 値等)への**不可逆変換点が無い**(gate の 3 値写像は appliedMapping で可逆に記録) |
| D2 丸め禁止の CI 版 | gate-policy は scope 種別ごとの閉写像を必須(fail-closed、§3.2.1)。さらに **unmeasured / unknown / not_computed / violated-assumption-dependency の写像先は `pass_with_boundary` / `block` の 2 値に schema 制限**され、plain pass の割り当ては validation fail。非終端 verdict が痕跡なく通る経路は制度選択としても存在しない |
| D3 structural / analytic 分離 | analyticReadings の `claimStatus` / `fidelity` 型区別。candidate reading は verdict の根拠にできない(packet validation)。gate は structuralVerdicts のみを写像対象とし、analytic 値の閾値 gate は v0.5.0 では提供しない |
| D4 6 区画保存 | packet v2 は定義11.1 の 6 区画を保持し、suppliedData / boundaryStatements を追加区画として拡張 |
| D5 nonConclusions は残すが主役化しない | packet に derived compat view として存続。summary / gate-report の headline は常に肯定的 conclusionCode |
| D6 unknown ≠ failure | gate-policy の写像語彙に `fail` が無い(`pass / pass_with_boundary / block`)。exit code も gate 判定であって計測の成否ではない |
| C1 一括払い(観測ヘッジを ArchSig 内部に分散しない) | 観測の穴は frontier という**観測層宛て artifact** に一括して出す。ArchSig 本体は補完・推測・fallback を持たず、計測は選ばれた profile 内で完結した肯定的結論を出す。frontier entry の disposition 分類(private / unavailable / out-of-scope)も authoring 層の所有であり ArchSig は埋めない(§3.4 規則 4) |
| C2 ArchMap は "X is the case" のみ | frontier の `neededObservation` は生観測の形だけを要求。delta にも diagnostic-shortcut 検査を適用 |
| C6 判定・比較・計算は ArchSig が独占 | comparison data は写像のみを供給し(anti-weakening hard error)、transport の計算と結論は ArchSig が行う。transport は kind ごとの licensed conclusion 形に限定され、方向違反は validation fail(§3.3.2)。supplied 台帳に適合条件検査を記録 |
| C7 viewer は verdict を作らない | viewer data v3 の drivenBy 必須 + 結論文字列照合を機械検査化(ArchView マイルストーン) |
| C8 FieldSig は explicit handoff | measurement packet v2 が唯一の handoff。raw packet 経路は削除 |
| B1/B2 無制限 claim・extraction completeness の排除 | frontier は選択 evaluator 相対の有限要求のみ。`silence_by_design` / `out_of_selected_vocabulary` からは要求を生成しない。comparison の 3 段階 + kind 別 license は「comparison data なしの cross-run 主張」「理論が遮断した方向の transport」を構造的に不可能にする(第X部 命題4.10・定理8.4/8.5 の遮断をそのまま artifact 契約化) |
| B4 主張の種類を混ぜない | claimStatus(certified/candidate)、fidelity(faithful/proxy)、suppliedData(supplied/generated)の三対で、packet 上の全主張が型を持つ。comparison の conclusionCode は record 水準(RECORDED 系)と transport 水準(licensed 系)を名前の水準で分離 |

**tool 設計上の選択と理論由来の制約の区別**(B6): 5 値 verdict・6 区画・comparison-is-data・concrete class・refinement の片方向性は AAT 本文由来(第IV部 4.4、第VIII部 3.1/3.2/7.2/7.3/11.1、第X部 4.10/7.1/8.4/8.5)。gate の 3 値写像語彙、frontier の導出規則、exit code 体系、命名規約、digest 正規化は tool 設計上の選択である。

---

## 5. 移行とリスク

### 5.1 移行順序(archsig-code レポートの 3 段階削除と整合)

AG path は v0/v1 とコード独立なので、artifact 再設計は legacy 削除と並走できる。**v0.5.0 の出荷ゲートは Phase A–C**。Phase D 以降を同一版に積まない — schema 新設 / bump 約 13 件 + 新サブコマンド 3 + CI e2e 全面置換 + golden corpus 再編は一版で運ぶ量ではなく、さらに viewer v3 は ArchView 再設計(次元 6)の決定に依存するため、同一マイルストーンに束ねるとどちらかの遅延が全体を止める。

1. **Phase A(v0.5.0)**: 命名統一(schema キー / slash 形式。viewer data のみ例外的に v2 のまま、§3.0/§3.6)、run manifest v3、Cargo version 0.5.0、sha2 依存追加 + digest 基盤(§3.0.1)、toolVersion / inputDigests 埋め込み、schema-catalog v1(deprecated 区分導入)。孤児ファイル削除と同時でよい。
   **書き換え面の見積り**: `tests/cli.rs` は 17,346 行で schema 文字列への断言が 150 箇所超あり、命名統一だけで大半に波及する。機械的置換スクリプトを用意し、Phase A を独立 PR にして diff を隔離する。
   **同時更新(SKILL / docs)**: archsig-reader の `SKILL.md` + `references/output-reading-guide.md`、law-policy-creater の `references/schema-guide.md` にハードコードされた artifact 名・schema 文字列(`schemaVersion` キー、hyphen 版数、summary / manifest の現行名)。
2. **Phase B(v0.5.0)**: packet v2(**単一切替、dual-emit なし**)。packet validation v2。summary v3 / insight v2。FieldSig の v2 受理 + 行レベル propagation + v0/v1 受理コード削除(§3.5)。同時更新: 上記 SKILL references の packet 節。
3. **Phase C(v0.5.0)**: `archsig gate` + gate-policy 導入、`--strict-distance` 廃止。CI e2e 前半の置換(`--manifest-path` 形式、§3.11)。starter gate-policy テンプレート + docs/tool の gate-policy authoring ガイド(§3.2.1)。pr-review コマンドは deprecated 告知(削除は Phase D)。
4. **Phase D(0.5.x 追補)**: `archmap-delta/v1` + `delta-apply` + `compare`、pr-review コマンドと archmap-delta-v0 の削除(= v1 path 削除 ③ と同時)。pull_request 側 CI の delta gate 追加。archsig-pr-reviewer SKILL の v2 後継へ改稿。
5. **Phase E(0.5.x、ArchView 再設計マイルストーンと同期)**: frontier 出力 + archmap-creater SKILL の frontier 読み対応(作業台帳への disposition 分類を含む、§3.4)。viewer data v3。
6. **Phase F(0.6.0)**: v0 dead コード + catalog deprecated エントリの削除。

各 Phase は「schema + validation + fixture + docs(commands.md / artifacts-and-boundaries.md / README)+ golden corpus + 上記 SKILL references」の同時更新を含む(D7)。

### 5.2 リスクと対策

| リスク | 対策 |
| --- | --- |
| スコープ肥大で v0.5.0 が滑る(schema 13 件 + サブコマンド 3 + CI 置換 + corpus 再編) | 出荷ゲートを Phase A–C に限定(§1、§5.1)。packet v2 の profile は MeasurementProfileV1 埋め込みで凍結し LawPolicy 再設計を待たない(§3.1)。viewer v3 は ArchView マイルストーン側に置き、どちらの遅延も他方を止めない |
| frontier が「残タスク一覧」「未完了の証明」として読まれる | (a) 導出源を intended-scope 内 + 3 boundary kind に限定、(b) summary headline から排除し authoring 区画に配置、(c) `discipline` 文字列を schema 必須にし fixture で lock、(d) SKILL 側の読み方指示(complete-first の修理キューとして扱う)を同 PR で改稿 |
| gate-policy の作者が verdict を実質的に丸める | 非終端 verdict への plain pass は **schema 水準で不可能**(写像先 2 値制限、validation fail。§3.2.1)。加えて明示写像必須(省略 = validation fail)+ appliedMapping の全行記録 + starter テンプレートは保守的既定(unmeasured/unknown → pass_with_boundary、not_computed/violated → block)で同梱 |
| comparison data の authoring コストが高く、PR review が常に not-comparable に落ちる | level 2(verdict-row)を自動判定にし、**contexts / covers に触れない delta(最頻ケース: 実装変更で section 値だけ変わる)では comparison data 不要**。identity comparison は digest 一致から自動導出 |
| 単一切替(dual-emit なし)が外部利用者を壊す | release asset は archsig バイナリのみで fieldsig は配布されておらず、特定できる外部 packet 消費者が存在しない(§3.5)。仮に release バイナリの packet を独自スクリプトで読む外部者がいても、Phase A の命名統一(schema キー / slash 形式)自体が breaking であり、packet 単独の dual-emit は救済にならない。v0.5.0 を breaking release として release note + catalog deprecated エントリで告知し、旧 pipeline は v0.4.x バイナリで継続可能とする |
| exit code 意味変更(現行: analyze が validation 失敗で exit 1)による CI 破壊 | Phase A で exit 2 へ変更し、lean.yml を同 PR で更新。release note に breaking として明記 |
| conclusionCode registry と summary 文言のドリフト | registry を単一 const 定義 + catalog 掲載 + fixture lock の三点固定 |
| golden corpus の書き換え量 | corpus 文書を「AG v2 系 + 新 artifact 系」に再編し、v1/v0 節は archive へ移動。決定論 lock(digest 同一性)で fixture 本数の増加を抑える。Phase 分割により 1 PR あたりの書き換え範囲を制御 |
| viewer data v3 の drivenBy 検査が既存投影を壊す | Phase E を ArchView 再設計(次元 6)と同一マイルストーン(0.5.x)に束ね、投影対象の allowlist を両側から同時に決める。v0.5.0 本体はこのマイルストーンに依存しない |

---

## 6. 未決事項

1. **MeasurementProfile の独立 artifact 化**(LawPolicy 再設計次元)。v0.5.0 の packet v2 は既存 `MeasurementProfileV1` の埋め込み + `profileFingerprint` で**凍結済み**(§3.1 本文)なので、この決定は v0.5.0 をブロックしない。独立 artifact 化された場合も packet 側は fingerprint の算出元が変わるだけ。
2. **SAGA 系 evaluator の invariant kind / suppliedData kind の確定**(AG 分析次元)。本設計は予約枠(§3.7)のみ。特に faithfulness data / semantic projection を archmap/v2 拡張として運ぶか独立入力 artifact にするかは ArchMap 次元との合議。
3. **gate の analytic 閾値**(例: harmonic mass 上限)。D3 との緊張が強いため v0.5.0 では見送り、structural verdict gate のみ。将来入れるなら「analytic gate は verdict と別レーンの `advisory` outcome に限る」等の設計が要る。
4. **SARIF 等の標準 CI フォーマット出力**。GitHub annotation との親和性は高いが、SARIF の severity 語彙への写像が verdict 丸めの温床になる。gate-report → SARIF は変換器を別コマンド(または SKILL)として切り出す案までで保留。
5. **ArchMapStore 本体**(commit / snapshot / index)の復活時期と、FieldSig longitudinal 責務との線引き。v0.5.0 は delta のみ。
6. **frontier を FieldSig へも流すか**(観測需要の時系列を SFT 信号にする案)。境界的には可能に見えるが、v0.5.0 スコープ外として保留。
7. **`--stamp` の既定化判断**: runId の既定は決定的導出で確定(§3.0.1)。時刻 suffix を CI 以外の対話利用で既定にするかは運用実績を見て決める。
8. sources 台帳への git revision / content hash 追加は ArchMap schema(次元 2)の管轄。本設計の delta-apply は archmap 全体 digest で stale 検出できるため依存しないが、entry 単位の鮮度検証には将来必要になる。

---

## 査読対応

査読 1 巡目の指摘 11 件の採否。事実主張は一次ファイルで検証した(root Cargo.toml 不在、archsig-release.yml の配布物 = archsig バイナリのみ、tests/cli.rs 17,346 行 + schema 文字列断言 150 箇所超、両 Cargo.toml の依存 = clap/serde/serde_json/walkdir のみ、archsig-reader / law-policy-creater の references に schema 文字列ハードコード、law_policy.md の residual gap 規律)。

| # | 指摘 | 採否 | 対応 |
| --- | --- | --- | --- |
| 1 | authoringDisposition の割り当て主体未定義(boundary/minor) | **採用(提案 (2) を選択)** | disposition フィールドを frontier schema から**削除**(§3.4)。frontier は run ごとに再生成される ArchSig 出力なので、author 記入フィールドを持たせても永続しない(提案 (1) の難点)。分類は archmap-creater SKILL の作業台帳が所有し、law_policy.md の residual gap 規律に従うことを生成規則 4 と discipline 文字列に明記。「表現可能か」の機械判定フィールドも、生成規則 2 により全 entry が定義上表現可能なため不要と判断 |
| 2 | comparability level → conclusionCode 対応表の欠如、deltaRefs 帰属規則未指定(boundary/minor) | **採用** | §3.3.2 に level → 発行可能 conclusionCode の対応表を追加。CLEARED/INTRODUCED 系は record 水準の名称(`…_RECORDED_AFTER_CHANGE` / `…_NO_LONGER_RECORDED_AFTER_CHANGE`)へ改名し、claim 形(同一 profileFingerprint + siteCoverDigest 下の verdict 記録の遷移であり class transport ではない)を規範として固定 + discipline 文字列化。deltaRefs は「delta op の対象 id と verdict 行の参照 id の機械的交差、空なら []、因果帰属ではない」と導出規則を明記 |
| 3 | class-transport 行が方向・kind 無限定(theory/major) | **採用** | §3.3.2 に kind 別 license 表を新設: refinement = 粗→細片方向のみ(命題4.10)、逆方向は定理8.5 の反例(Lean: `refinementZeroComparison_not_unconditional_for_coarseZero_fineNonzero`)により typed boundary として沈黙; refactor-morphism = pullback reading(定義7.2)のみで、zero iff は定理7.3 の仮定を equivalenceData の conformance 検査として要求; identity = 双方向。measurement-comparison/v1 の refinement kind に `tripleMap` と δ⁰ 可換性・residual 引き戻し自然性の適合条件を必須化(§3.3.3)。comparison-report に `transport.direction` を置き、licensed 方向・結論形の違反を validation fail に(§3.3.2) |
| 4 | 「どの水準でも transport 主張を自動生成しない」と CLEARED/INTRODUCED 系の内部緊張(theory/minor) | **採用(#2 と統合)** | conclusionCode の record 水準への改名 + claim 形固定で「どの水準でも」の文と整合させた。transport 主張は class-transport 水準の licensed conclusion(`ZERO_PRESERVED_UNDER_REFINEMENT` 等)としてのみ、供給・検査済みデータの下で発行されると本文で明示。deltaRefs の非因果性は #2 の導出規則 + discipline で固定 |
| 5 | D2 主張(unmeasured→pass でも痕跡が残る)と schema 仕様の食い違い(theory/minor) | **採用(強い側の修正を選択)** | gate-policy validation で非終端 verdict(unmeasured / unknown / not_computed / violated-assumption-dependency、および introduced-by-change の removed / other)の写像先を `pass_with_boundary` / `block` の 2 値に制限し、plain pass を validation fail に(§3.2.1)。§4 D2 行と §5.2 リスク行を機構と一致する記述に更新。D2 の弱化(記述を appliedMapping 記録に弱める案)ではなく schema 制限を選んだのは、丸め禁止 CI 版という設計主張を機構で支える方が第VIII部 原則3.2 に忠実なため |
| 6 | スコープ肥大と他次元への結合(feasibility/major) | **採用** | v0.5.0 出荷ゲートを Phase A–C に明示限定(§1、§5.1)。Phase D は 0.5.x 追補、Phase E は ArchView マイルストーンへ切り出し。§6.1 のヘッジを §3.1 本文に昇格し「MeasurementProfileV1 埋め込み + profileFingerprint で凍結、LawPolicy 再設計を待たない」と明記。tests/cli.rs の書き換え波及(17,346 行 / 断言 150 箇所超)を Phase A の見積りとして記載し、独立 PR + 置換スクリプトで隔離。§5.2 にスコープリスク行を追加 |
| 7 | fail-closed 規律が自らの例と矛盾、introduced-by-change の定義域未規定(feasibility/minor) | **採用** | fail-closed を scope 種別ごとに再定義(§3.2.1): absolute = 6 写像必須、introduced-by-change = 閉じた 5 カテゴリ(new / cleared / preexisting / removed / other)への写像必須。5×5 遷移 + added/removed 行の機械分類規則を確定し、例 rule を 5 キーすべて明示の形に修正 |
| 8 | digest 基盤が仕様未定のまま load-bearing(feasibility/minor) | **採用** | §3.0.1「digest / 決定論基盤」を新設: (1) sha2 依存追加を明記、(2) 正規化 = serde_json::Value 経由の compact 再直列化(BTreeMap キー順)+ SHA-256、生バイト digest の不採用理由、RFC 8785 非準拠の判断根拠(外部相互運用要件なし)、(3) siteCoverDigest の対象フィールド列挙(contexts / covers / 導出 nerve のみ、atoms / sources 非依存)、(4) runId の決定的導出規則。§3.0 の runId 例から日付を除去し §3.9 と整合させた |
| 9 | CI YAML の `cargo run -p` が root workspace 不在で動かない(feasibility/minor) | **採用(--manifest-path 形式を選択)** | §3.11 の YAML を現行 lean.yml と同じ `--manifest-path` 形式に修正。workspace 化はスコープ外と明記(採るなら .lake / CI キャッシュ影響確認を伴う独立 Issue) |
| 10 | FieldSig 両受理窓と packet dual-emit の受益者不在(feasibility/minor) | **採用(両方削除)** | archsig-release.yml を確認し、release asset は archsig バイナリのみで fieldsig は非配布と確定。FieldSig の v1/v2 両受理窓を削除し atomic 切替に一本化(§3.5)。packet dual-emit(`--emit-packet-v1-compat`)も削除 — 仮に外部 packet 消費者がいても Phase A の命名統一自体が breaking であり、packet 単独の dual-emit は救済にならない(§5.2)。告知は release note + catalog deprecated エントリで行う |
| 11 | SKILL 改稿予算の漏れ(feasibility/minor) | **採用** | Phase A/B の同時更新対象に archsig-reader(SKILL.md + references/output-reading-guide.md)と law-policy-creater(references/schema-guide.md)を明記(§5.1)。gate-policy の authoring 責務を §3.2.1 に追加: 専用 SKILL は新設せず starter テンプレート + docs/tool の authoring ガイドで賄い、law-policy-creater の管轄に入れない(law の選択と CI 制度の選択を混ぜない) |

11 件すべて妥当と判断し反映した。棄却した指摘はない。指摘が複数案を提示した箇所(1, 2/4, 5, 9)は上表の通り選択理由を付した。
