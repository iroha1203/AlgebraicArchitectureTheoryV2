> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計ノート — 設計次元6: ArchMap 抽出 Agent SKILL の再設計(漏れなく・再現性高く)

作成日: 2026-07-04(査読反映改訂: 同日)
対象: `tools/archsig/skills/archmap-creater`(SKILL 本体・references・candidate packet 書式)と、それを支える ArchSig 側の authoring 支援 CLI・authoring artifact 契約。
関係文書: 調査レポート skills-workflow / archmap-lawpolicy / philosophy / archsig-code / saga(scratchpad/archsig_v050/)、`docs/tool/archmap_observation_purity_prd.md`、`docs/tool/archmap_lawpolicy_archsig_responsibility_charter.md`。

---

## 1. 目的

ArchMap v2 の作成(リポジトリ証拠 → `archmap/v2` JSON)を、次の 2 性質を検査可能な形で満たす Agent SKILL に再設計する。

1. **再現性**: 同一リポジトリ・同一スコープ・同一 revision から SKILL を 2 回実行したとき、得られる atoms / contexts / covers が正規化キーの水準で高い一致率を持ち、不一致が手続き上どこで生じたかを artifact から追跡できること。
2. **網羅性(bounded)**: ユーザーが選択したスコープの内側について「何を走査し、各 source から何を得たか」の記録が artifact として残り、走査漏れが機械検査で浮上すること。**extraction completeness(スコープ外を含む完全抽出)は主張しない。** 主張は常に「選択スコープ内の走査記録」という bounded claim に留める。

設計の中核は次の一行に集約される。

> **機械層(列挙・ハッシュ・突合・参照整合)と読解層(atom の生成・採否・意味付け)を明示的に分離し、機械層を決定的にし、読解層を二重化して突合する。**

これは現行 SKILL の反スクリプト規律(最終 atom のスクリプト生成禁止)を破らない。スクリプトが許されている 2 用途(候補列挙・検証)を binary のコマンドとして整備し、そこに再現性の底を作る。読解と意味付けは従来どおり LLM の主観的読み(責務憲章 原則2「主観はバグではなく機能」)のまま守る。

---

## 2. 現状の問題(現行 archmap-creater SKILL の弱点分析)

調査レポート(skills-workflow §2.3–§4、archmap-lawpolicy §6)で file:line まで確認済みの事実に基づく。

| # | 弱点 | 具体的な所在 | 帰結 |
| --- | --- | --- | --- |
| W1 | **再現性を測る装置がゼロ** | golden corpus は「手書き fixture → binary 出力」の lock のみ。同一スコープでの再抽出を突合する diff ツール・照合 corpus が存在しない | 「検出精度が課題」という認識に対する計器が無く、改善が測れない |
| W2 | **品質ゲートが自己申告ブール 4 個** | prompt-pack.md:69-83 の `notScriptGenerated` 等。機械検証と接続していない | ゲートが LLM の自己評価に依存し、実行ごとに基準が揺れる |
| W3 | **スコープと走査の記録が artifact を持たない** | スコープは依頼文レベル(SKILL.md:62)。未読在庫は schema なしの notes 行き。「何を読まなかったか」の機械可読な記録が残らない | 漏れの検出が complete-first ループ(選ばれた cover の内側)に閉じ、cover 外・atom 化されなかった source の漏れは一切浮上しない |
| W4 | **語彙が自由文字列で dedup が字面一致** | v2 は predicate / axis / subject とも非空検査のみ(archmap.rs:382-414)。dedup キーは字面一致(repository-survey.md:40) | 計測面への波及は二段。**(直接)** `sectionValue` atom の object 字面揺れは cech mismatch 計算に直接効く(`cech_section_values` は BTreeSet\<String\> の字面比較。ag_measurement.rs:9622-9694。同義語の揺れが偽 mismatch を作る)。**(間接)** `placesOrder` / `createsOrder` のような capability 系 predicate の揺れは、意味的重複の残留と context / cover の切り方のぶれを通じて計測面へ波及する(cech 経路は context の atom 族を直接読まないため、直接因果は sectionValue 側にある) |
| W5 | **sources に revision / content hash が無い** | ArchMapSourceV1 は kind/path/symbol/line 等のみ(schema/archmap.rs:119-135) | ArchMap がどのコミット時点の観測かを artifact から復元できず、鮮度検査・CI 連携・PR レビューの土台が無い |
| W6 | **context / cover / restrictsTo の選択規準が薄い** | context cue は 6 例の列挙のみ、cover 選択規準は循環気味(mapping-guide.md:93-96)、restrictsTo の操作的定義が無い | cover は AG 計測の測定面そのもの。切り方のぶれが計測結果のぶれに直結する |
| W7 | **semantic の密度とalias 保存の規律が無い** | 同一リポで semantic atom が 3 個にも 30 個にもなり得る。同一 component に射影される相異なる semantic atom(alias)を dedup で潰しても検出されない | SAGA(第X部)の faithfulness 判定は alias(Λ/K 二層)の観測が核心(例2.6/3.6)。alias を潰す抽出は SAGA の十分性方向の入力を退化させる |
| W8 | **既知 gap 類型が survey surface に載っていない** | 実測で確認済みの coverage gap 類型(per-file semantic / runtime trace / permission audit、aat_ag_porting_bridges_grand_theorems.md:428)が repository-survey.md の目安リストに明示されていない | 同じ型の漏れを繰り返す |
| W9 | **SKILL 間の版数ねじれ** | archmap-creater は v2 一次だが archsig-reader / archsig-pr-reviewer は v1 前提。complete-first ループが v2 で閉じない | 本設計次元の隣接課題(レガシー破棄・artifact 再設計次元と接続)。本ノートでは creater 側の接続点だけ定義する |

---

## 3. 設計案

### 3.1 全体データフロー

```
ユーザーのスコープ指定(include/exclude + 依頼文)
   │ (0) preflight: binary 解決・git revision 取得・スコープ承認
   ▼
archsig scope-manifest ──────────────► authoring/scope-manifest.json   … 決定的 worklist(機械層)
   │ (worklist を固定 chunk に決定的分割)
   ├─► pass A: 並列 sub-agent 読解 ──► authoring/candidates/pass-a-<chunk>.json
   └─► pass B: 独立 sub-agent 読解 ──► authoring/candidates/pass-b-<chunk>.json
   │        (candidate packet = 候補 atoms/contexts/covers + survey 行。読解層)
   ▼
archsig extraction-diff ─────────────► authoring/consistency.json      … 正規化キー突合(機械層)
   │ (unmatched を integrator が「該当 source の再読解」で裁定。読解層)
   ▼
integrator 統合 ─────────────────────► archmap.json                    … 最終 ArchMap(読解層)
   │                                    authoring/coverage-ledger.json … 走査記録(機械層+記録)
   ▼
archsig archmap --input archmap.json \
  --scope-manifest … --candidate-packets … --coverage-ledger … ──► archmap-validation.json
   │ (既存 v2 lint + authoring 監査。機械層)
   ▼
(LawPolicy があれば)archsig analyze → complete-first 修理ループ(従来どおり)
```

ArchMap 本体(`archmap/v2`)の schema は**変更しない**。新設 artifact はすべて ArchMap の外側(authoring workspace)の sibling artifact であり、計測経路(`analyze`)は一切読まない。

### 3.2 新設 authoring artifact(4 schema、JSON フィールドレベル)

#### (1) `archmap-scope-manifest/v1` — スコープ台帳と決定的 worklist

`archsig scope-manifest` コマンド(§3.3)が生成する。**再現性の底**: 同一ツリー・同一 spec からはビット同一の worklist が出る。

```json
{
  "schema": "archmap-scope-manifest/v1",
  "id": "scope:orders-service:2026-07-04",
  "repository": {
    "root": ".",
    "revision": "git:3f9c2a7e…(40-hex)",
    "dirty": false
  },
  "scopeSpec": {
    "includeGlobs": ["src/**/*.rs", "docs/architecture/**/*.md"],
    "excludeGlobs": ["**/target/**", "**/vendor/**"],
    "addedEvidence": ["trace:orders-happy-path=authoring/evidence/orders-happy-path.trace.json"],
    "requestedScope": "orders service and its provider boundaries",
    "approvedBy": "user"
  },
  "worklist": [
    {
      "order": 1,
      "sourceId": "src:docs/architecture/orders.md",
      "path": "docs/architecture/orders.md",
      "kind": "doc",
      "contentHash": "sha256:…",
      "sizeBytes": 4813,
      "authorAdded": false
    },
    {
      "order": 214,
      "sourceId": "trace:orders-happy-path",
      "path": "authoring/evidence/orders-happy-path.trace.json",
      "kind": "trace",
      "contentHash": "sha256:…(上記ファイル内容のハッシュ)",
      "sizeBytes": 90211,
      "authorAdded": true
    }
  ],
  "exclusions": [
    { "path": "src/vendor/**", "reason": "user-excluded" },
    { "path": "ops/secrets.md", "reason": "private" }
  ]
}
```

- **決定的走査順序**: `worklist[].order` は path の byte 単位辞書順で採番する。author が追加する非ファイル証拠(trace、生成 artifact、供給された permission audit 等)は `authorAdded: true` でファイル worklist の後ろに、sourceId の辞書順で連結する。
- **author 証拠の投入機構**: author 追加証拠は必ず**ファイルとして供給**し、`archsig scope-manifest --add-evidence <kind>:<name>=<repo相対path>` の明示フラグで登録する(manifest の手編集は禁止)。`contentHash` は供給ファイル内容の sha256、`path` はそのファイルの repo 相対 path。`--add-evidence` は `scopeSpec.addedEvidence` として manifest に記録されるため、**再実行・`--baseline` 増分でも author 証拠は spec の一部として保持・再現される**。
- `sourceId` 規約: ファイルは `src:<repo相対path>`、trace は `trace:<name>`、doc 節は `doc:<path>#<section>`。ArchMap の `sources` キーはこの sourceId を使う。これは現行 fixture の短縮ラベル慣行(`src:top` / `src:order` 等)の**変更**(repo 相対 path 化)であり、規約化ではない。既存 fixture は計測経路・従来の単体検証の対象のままであり、authoring 監査(§3.3c)は authoring フラグを与えた場合のみ実行されるため、fixture は authoring 監査対象外(互換問題は生じない)。
- `exclusions[].reason` は**スコープ確定時(Workflow 段階2)の**手続き記録の統制語彙: `user-excluded | private | generated | binary | out-of-scope`。非難や欠陥の語彙ではない(走査しなかった理由の記録)。`out-of-scope` はスコープ確定・再承認の時点でのみ使える語彙であり、pass 実行中の skip 理由には使えない(§3.2(2)・§3.5 段階3)。
- `repository.revision` がこの authoring 一式の鮮度の一次記録になる(W5 への一次回答。ArchMap 本体への revision 追加は §6 未決事項)。

#### (2) `archmap-candidate-packet/v1` — sub-agent の候補パケット(抽出ログを内包)

現行 prompt-pack.md の非公式 JSON を schema 化・拡張する。**抽出 provenance(何を走査しどの atom を得たか)は `surveyRows` としてここに残る。**

```json
{
  "schema": "archmap-candidate-packet/v1",
  "id": "candidates:pass-a:chunk-03",
  "scopeManifestRef": "scope:orders-service:2026-07-04",
  "passId": "pass-a",
  "chunk": { "worklistOrderFrom": 41, "worklistOrderTo": 60 },
  "reviewedSources": ["src:src/orders/handler.rs"],
  "candidateSources": {
    "src:src/orders/handler.rs": { "kind": "file", "path": "src/orders/handler.rs" }
  },
  "candidateAtoms": [
    {
      "id": "atom:capability:orders.Handler:handlesPlaceOrder",
      "kind": "capability",
      "subject": "orders.Handler",
      "axis": "static",
      "predicate": "handlesCommand",
      "object": "PlaceOrder",
      "refs": ["src:src/orders/handler.rs"]
    }
  ],
  "candidateContexts": [],
  "candidateCovers": [],
  "surveyRows": [
    {
      "sourceId": "src:src/orders/handler.rs",
      "status": "read",
      "surveyedKinds": ["component", "relation", "capability", "authority", "contract", "semantic"],
      "candidateAtomIds": ["atom:capability:orders.Handler:handlesPlaceOrder"],
      "notes": []
    }
  ],
  "privateUnavailableNotes": [],
  "selfReview": {
    "notScriptGenerated": true,
    "notCoarseWhenEvidenceWasRicher": true,
    "semanticAtomsHaveUseEvidence": true,
    "noDiagnosticShortcutAtoms": true,
    "worklistChunkFullyRead": true,
    "aliasPreservingSemantics": true
  }
}
```

- `surveyRows[].status` は `read | partial | skipped` の三値。`partial` / `skipped` には `notes` で理由を付ける。理由の統制語彙は**手続き理由に限定**する: `private | binary | unreadable | tooling-error`。**`out-of-scope` は使えない**。worklist はユーザー承認済みのスコープ表明であり、スコープ判断を pass 実行中の sub-agent / integrator に分散させない(境界の一括払い)。読解中に「これはスコープ外だ」と判明した source の扱いは §3.5 段階3 の round-trip 規則(scope manifest 更新+ユーザー再承認)による。
- `surveyRows[].surveyedKinds` は「この source をどの atom kind の目で走査したか」の記録。**「走査したが該当 atom を観測しなかった」は、candidateAtomIds に載らないことで表現される**。これは世界についての measured absence ではなく、authoring 手続きの記録である(§4 参照)。
- self-review gate は 4 → 6 に拡張(新規: `worklistChunkFullyRead`=担当 chunk の全 worklist 行に surveyRow がある、`aliasPreservingSemantics`=同一 subject に相異なる use-evidence があるとき別 atom として保持した)。うち `worklistChunkFullyRead` と `noDiagnosticShortcutAtoms` は §3.3 の機械監査で裏取りされる(自己申告からの昇格)。

#### (3) `archmap-extraction-consistency/v1` — 二重抽出の突合レポート

`archsig extraction-diff` が生成し、integrator の裁定記録を追記して確定する。

```json
{
  "schema": "archmap-extraction-consistency/v1",
  "id": "consistency:orders-service:2026-07-04",
  "scopeManifestRef": "scope:orders-service:2026-07-04",
  "passARefs": ["candidates:pass-a:chunk-01", "candidates:pass-a:chunk-02"],
  "passBRefs": ["candidates:pass-b:chunk-01", "candidates:pass-b:chunk-02"],
  "atomMatchKeySpec": "atom-match-key@1",
  "matched": { "count": 132 },
  "onlyInPassA": [
    { "key": "capability|orders.Handler|static|handlesCommand|CancelOrder",
      "candidateAtomId": "atom:capability:orders.Handler:handlesCancelOrder",
      "refs": ["src:src/orders/handler.rs"] }
  ],
  "onlyInPassB": [],
  "matchRate": 0.992,
  "contextDiff": { "matched": 14, "onlyInPassA": [], "onlyInPassB": ["ctx:provider-mediation"] },
  "adjudications": [
    { "key": "capability|orders.Handler|static|handlesCommand|CancelOrder",
      "decision": "adopted",
      "basis": "re-read src:src/orders/handler.rs (cancel path exists; pass B chunk boundary cut it)" },
    { "key": "…",
      "decision": "not-adopted",
      "basis": "duplicate of atom:… after subject normalization" }
  ]
}
```

- **atom-match-key@1**(正規化キー仕様): `kind | NFC(trim(subject)) | axis | predicate? | object?`。`refs` はキーに含めない(pass 間で行参照が微妙に違っても意味的同一なら match させ、refs は統合時に和集合)。`id` もキーに含めない(id は pass 間で揺れてよい)。**semantic kind は例外規約を持つ**: 意味内容を必ず `object` に載せる(vocabulary-catalog の object 必須規約、§3.4)ため、意味差はキーに常に反映される。仕様には `matchRate = matched / (matched + |onlyInPassA| + |onlyInPassB|)` の定義式を併記する(上例: 132 / 133 ≈ 0.992)。
- `matchRate` は **数値記録であり verdict ではない**。閾値による自動合否を設けない。SKILL が課すのは「`onlyInPassA/B` の各項目を、必ず該当 source を再読解して `adjudications` に裁定を書く」という手続きのみ。裁定語彙は中立: `adopted | merged | not-adopted`。
- contexts / covers は atom より構造的なので、context の match key は `sorted(member atom-match-keys) | sorted(restrictsTo 先の match keys)` で突合し、不一致は「切り方の相違」として integrator の裁定対象にする(W6 のぶれをここで顕在化させる)。

#### (4) `archmap-coverage-ledger/v1` — 選択スコープ内の走査記録(bounded claim)

integrator が candidate packet の surveyRows から生成する。**rows は worklist と 1:1**(全行をちょうど 1 回ずつ張る)であることが機械監査の対象。スコープ外の記録は ledger に持たず、scope manifest の `exclusions` への参照に一本化する。

```json
{
  "schema": "archmap-coverage-ledger/v1",
  "id": "coverage:orders-service:2026-07-04",
  "scopeManifestRef": "scope:orders-service:2026-07-04",
  "archmapRef": "archmap:orders-service",
  "passRefs": ["pass-a", "pass-b"],
  "rows": [
    {
      "sourceId": "src:src/orders/handler.rs",
      "surveyStatus": "surveyed",
      "passes": ["pass-a", "pass-b"],
      "surveyedKinds": ["component", "relation", "capability", "authority", "contract", "semantic"],
      "adoptedAtomIds": ["atom:capability:orders.Handler:handlesPlaceOrder"]
    },
    {
      "sourceId": "src:ops/runbooks/orders-oncall.md",
      "surveyStatus": "not_surveyed",
      "reason": "private"
    }
  ],
  "claimBoundary": "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness."
}
```

- `surveyStatus` は `surveyed | partially_surveyed | not_surveyed` の三値。`not_surveyed` / `partially_surveyed` には統制語彙の `reason` が必須。reason の語彙は surveyRows と同じ**手続き理由**(`private | binary | unreadable | tooling-error`)であり、`out-of-scope` は含まない(スコープ外は worklist に載らず exclusions に記録されるため、ledger 行になり得ない)。
- `claimBoundary` は定数 1 文(結論の隅に置く最小限の境界)。non-conclusion の一覧を持たない。
- この ledger が §2 W3 への回答: 「何を読まなかったか」が、ArchMap 本体を汚さずに、機械可読・監査可能な形で authoring 側 artifact に残る。

### 3.3 ArchSig 側の authoring 支援 CLI(機械層。3 面)

いずれも「候補列挙」と「検証」であり、atom を生成しない。計測経路(`analyze`)から完全に独立。

**新規依存**: `sha2`(contentHash)/ `unicode-normalization`(atom-match-key@1 の NFC)/ `globset`(include/exclude glob と、`--candidate-packets 'authoring/candidates/*.json'` のような quoted glob 引数の展開)。いずれも pure Rust で build 時間影響は軽微(現行依存は clap / serde / serde_json / walkdir の 4 つ)。**glob 引数は shell 展開に依存せず binary 内で展開する**(CLI 仕様として明記)。NFC 依存を避ける縮退案は §6 に記載。

#### (a) `archsig scope-manifest` — 決定的 worklist 生成

```bash
${ARCHSIG_BIN:-archsig} scope-manifest \
  --repo-root . \
  --include 'src/**/*.rs' \
  --include 'docs/architecture/**/*.md' \
  --exclude '**/target/**' \
  --add-evidence 'trace:orders-happy-path=authoring/evidence/orders-happy-path.trace.json' \
  --out authoring/scope-manifest.json
```

- ファイル走査 → byte 辞書順ソート → sha256 → worklist 採番。git revision と dirty flag を記録(git が無ければ `revision: null` を記録して続行。補完しない)。
- `--add-evidence <kind>:<name>=<repo相対path>` で author 証拠ファイルを worklist に登録する(§3.2(1)。spec に記録されるため再実行で再現される)。
- `--baseline <old-scope-manifest.json>` を渡すと、contentHash が変わった/新規の source だけを worklist に載せた**増分 manifest** を出す(`baselineRef` フィールド付き)。増分更新・CI 連携(別設計次元の pr-review 後継)への接続点。

#### (b) `archsig extraction-diff` — pass 間突合

```bash
${ARCHSIG_BIN:-archsig} extraction-diff \
  --scope-manifest authoring/scope-manifest.json \
  --pass-a 'authoring/candidates/pass-a-*.json' \
  --pass-b 'authoring/candidates/pass-b-*.json' \
  --out authoring/consistency.json
```

- atom-match-key@1 / context match の計算は binary が行う(突合の再現性を LLM に依存させない)。
- candidate packet 段階で **既存の diagnostic-token lint(`check_archmap_v2_no_diagnostic_shortcuts` 相当)を候補 atoms にも適用**し、判定語を持つ候補はこの時点で fail させる(判定語の混入を統合前に止める。R3 の前倒し)。
- **semantic object lint**: `kind: "semantic"` の候補 atom が `object` を持たない場合は fail させる(vocabulary-catalog の object 必須規約の機械裏付け。§3.4。alias 保存をキー担持フィールドに載せるための規約)。
- `--pass-b` を省略した single-pass 運用では `passBRefs: []` と記録し、matched/onlyIn 系を省略した縮退形を出す(黙って dual-pass と同形にしない)。

#### (c) `archsig archmap` への authoring 監査フラグ追加

```bash
${ARCHSIG_BIN:-archsig} archmap \
  --input archmap.json \
  --scope-manifest authoring/scope-manifest.json \
  --candidate-packets 'authoring/candidates/*.json' \
  --coverage-ledger authoring/coverage-ledger.json \
  --out archmap-validation.json
```

authoring フラグ群は**任意**(従来の単体検証は不変)。与えられた場合、既存 v2 checks に加えて次の監査 checks を実行する:

| check id | 内容 |
| --- | --- |
| `authoring-sources-resolve` | ArchMap の `sources` キーが下記の解決規則で scope manifest に解決する |
| `authoring-provenance-closure` | 採用された全 atom id が、少なくとも 1 つの candidate packet の surveyRow(または consistency の adjudications)から追跡できる |
| `authoring-ledger-spans-worklist` | coverage ledger の rows が worklist の全 sourceId をちょうど 1 回ずつ張る(worklist と 1:1。余剰行も欠落行も fail) |
| `authoring-read-before-cite` | 採用 atom の refs が指す source は、いずれかの pass で `status: read`(または `partial` + 該当節)である |
| `authoring-revision-recorded` | scope manifest に revision が記録されている(dirty は報告のみ、fail にしない) |

`authoring-sources-resolve` の**解決規則**(v2 validation が atom / context / cover の refs をすべて sources キーへ解決させる仕様と両立させるため、明文化する):

1. `src:<path>` — worklist(authorAdded 行を含む)の `path` に直接一致。
2. `doc:<path>#<section>` — `<path>` 部で worklist のファイル行に解決(節単位の行は scope-manifest binary は生成しない。著者が sources 側で節を細分してよい)。
3. `trace:<name>` 等の authorAdded 系 — worklist の authorAdded 行に sourceId 直接一致。
4. **grounding sources の免除**: context / cover の grounding のために sources に登録されるエントリ(`ctx:*` キーや、policy 文書節を指す `kind: "policy"` エントリ。現行 fixture `archmap_v2_cech_h1_visible.json:34-53` の慣行)は、走査対象ファイルではないため worklist 解決を**免除**する。免除は kind ベース(`policy` 等)の免除リストとして check 仕様に列挙し、無条件のワイルドカード免除にはしない。

- 監査結果の結論は肯定形を先頭に: 全 check 通過なら `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE`。不通過は該当 check の対象(source id / atom id)だけを列挙する(non-conclusion の羅列をしない)。
- これにより自己申告ゲートのうち `worklistChunkFullyRead`(← ledger-spans-worklist)、`noDiagnosticShortcutAtoms`(← 既存 R3 + extraction-diff の前倒し lint)、および provenance の実在(← provenance-closure)が**機械検証に昇格**する。`notScriptGenerated` と semantic の use-evidence 判断は自己申告+integrator 裁定のまま残す(機械化すると読解層を侵す。§4)。

### 3.4 SKILL 本体の再設計(構造案)

既存 4 SKILL の書式慣行(frontmatter 2 キー、Purpose → 規律 → Inputs → Rules → Workflow → Commands → Output Shape → References、release-bundle 自立性、binary 解決順序、停止条件明文列挙、日本語応答指示末尾 1 行)に従う。skill 名は既存トリガー資産を保つため `archmap-creater` を継続。

```
tools/archsig/skills/archmap-creater/
  SKILL.md                      # 全面改稿(Workflow を §3.5 の 9 段階に)
  agents/openai.yaml            # 据え置き(display_name / short_description / default_prompt)
  references/
    schema-cheatsheet.md        # v2 schema + 新 4 schema(scope-manifest / candidate-packet /
                                #   extraction-consistency / coverage-ledger)の形状
    mapping-guide.md            # 改稿: alias 保存規律、restrictsTo 操作的手掛かり、cover 選択規準
    examples.md                 # 追補: 「alias 潰し」「coverage ledger の書き方」「chunk 境界での
                                #   context 分断」の良悪対例
    extraction-protocol.md      # 新設: 決定的走査・chunk 分割・二重抽出・integrator 裁定・
                                #   スコープ round-trip の手順。repository-survey.md はここに吸収して
                                #   削除する(survey surface の目安リストと W8 の gap 類型は本文書の
                                #   「Survey surface(走査面の目安と既知 gap 類型)」節へ移設)
    coverage-and-consistency.md # 新設: ledger / consistency の書式・読み方・裁定語彙
    vocabulary-catalog.md       # 新設: kind / axis / predicate 3 層の recommended token 表、
                                #   subject / atom id 命名規約、正規化規則(atom-match-key@1)
    prompt-pack.md              # 改稿: candidate packet を schema 付きで指示、gate 6 項
```

`vocabulary-catalog.md` の位置づけ(W4 への回答):

- predicate / axis は **closed enum にしない**(v2 validation は自由文字列のまま。語彙の適用は観測の主観として守る)。カタログは「同じ観測は同じトークンで書く」ための recommended token 表であり、doctrine 固定(`doctrine:aat-canonical@1`)の言語ゲーム内での**語の使い方の統一**装置。
- **カタログ外 predicate トークンの使用**は「この観測に既存トークンが当てはまらなかった」という**適用判断**であり、integrator の裁定記録を要件とする(語彙体系の拡張ではない)。
- **新 axis の導入は authoring run 内の裁定事項としない**。axis は AG 計測が読む構造的セレクタ(cech / square-free 等)であり、自由文字列 predicate より規律上重い。axis 表への追加は doctrine / registry 側の変更(§6.3 の registry manifest 方針、LawPolicy 再設計次元)への **escalation** として扱い、authoring run は既存 axis 表の内側でのみ書く(責務憲章 原則3・観測純化 PRD 原則3「観測者は doctrine を選ばない・名乗らない・拡張しない」と整合)。
- 収録内容(初版)は **kind / axis / predicate の 3 層を別表で分離**し、カテゴリ混同を構造的に防ぐ:
  - **kind 表**: v2 schema の 9 kind(closed enum。schema 由来)。
  - **axis 表**: `ag_measurement.rs` の axis フィルタ実測から**機械的に採録**する。AG 経路が消費する axis(`cech / square-free / section-factorization / tor / transfer / period / laplacian / witness / boundary-residue / restriction-compatibility / coherence / refactor` — ag_measurement.rs:2937, 7119-9214, 9627, 9874, 10458 の filter 文字列)と、fixture 実測に現れる記述用 axis(`static / restriction / relation / capability / effect / authority / semantic / specification / existence / boundary`)を**別列で区別**し、各 axis に「AG 経路が読むか」を明記する。**`support` は axis ではなく生値 predicate であり、axis 表には載せない**(ag_measurement.rs:9328 `is_raw_support_predicate`: predicate が `support | cooccurrence`)。
  - **predicate 表**: kind 別 recommended predicate 例(relation: `dependsOn / calls / implements / publishesTo / readsFrom / writesTo`、capability: `handlesCommand / servesQuery / exposesEndpoint`、authority: `requiresRole / checksPermission / scopesToOwner`、state: `persistsIn / transitionsTo / cachedIn`、effect: `enqueues / publishes / mutatesFile / callsProvider`、contract: `requires / ensures / shapedAs / retriesWith`、semantic: `meansInUse / identifiedBy / statusGates`、runtime: `observedCall / observedLatency`)。
  - **axis × predicate 対応表(AG 消費面)**: どの axis 上のどの predicate を AG 経路が読むかを 1 表に収録する。生値 predicate は**対になる axis と組で**収める: `cech × sectionValue`(cech mismatch の入力)、`square-free × support|cooccurrence`、`section-factorization × support|cooccurrence|witnessAssignment`、`laplacian × cellularCochain|cellularBoundary`、`period × periodIntegral`、`transfer × transferPairing|repairPath|groundCost`、`tor × commonAmbient|lawIdealGenerator`、`witness × violation`、`boundary-residue × restrictionColumn|boundarySection` 等。初版は grep による機械採録で作り、**M2 の層1 テストに「カタログ収録 axis / 生値 predicate × 評価器フィルタ値の突合 lint」を置いて将来の乖離を lock する**(§3.6)。この表が無いと、AG 経路が読まない axis を持つ atom が黙って計測から外れる(axis フィルタ不一致で退化する)ArchMap を推奨してしまう。
  - **semantic kind の object 必須規約**: semantic atom は意味内容(use-evidence が示す「使われ方」の同定子)を `object` に必ず載せる。schema 上 object は optional(schema/archmap.rs:85-86)だが authoring 規約として必須化し、candidate packet 段階の lint(§3.3b)で機械的に裏付ける。alias の区別を atom-match-key@1 のキー担持フィールドに載せるための規約(下記 alias 保存規律)。
  - subject 命名 `<domain-or-module>.<Symbol>`、atom id 規約 `atom:<kind>:<slug(subject)>[:<slug(predicate-or-object)>]`。
- law-policy-creater との接続点として、AG 計測が読む生値 predicate(`sectionValue` / `support` / `cooccurrence`)の書式例も上記対応表に収める(観測純化 R2 の入力形)。

`mapping-guide.md` への追補(W6・W7 への回答):

- **alias 保存規律(SAGA 接続の観測側要件)**: 同一 subject(component 粒度)に対し、相異なる use-evidence が観測されたら **semantic atom を別々に保持**する。「同じ component を指すから 1 個にまとめる」統合を明示的に禁止する。**この規律が機械 dedup(atom-match-key@1)で保たれるのは、意味差がキー担持フィールド(predicate / object)に載っている場合に限る**。そのため semantic kind は object 必須規約(vocabulary-catalog + §3.3b lint)で意味差を必ず object に載せる。加えて統合(§3.5 段階6)では、**key が完全一致し refs だけが異なる semantic atom 対の refs 和集合統合は機械で確定せず、integrator が「同一の意味か」を確認して確定する**(規約違反の取りこぼしに対する安全網)。これは第X部の semantic atom projection(Λ/K 二層、alias は fiber の非単射性)を観測側で潰さないための契約であり、faithfulness の判定自体は ArchSig / 理論側の仕事(観測は判定しない)。
- **restrictsTo の操作的手掛かり**: 現行 fixture(`archmap_v2_cech_h1_visible.json`)の実測では、包含する側の context から共有・重なり側の context へ向けて張られている(`ctx:top → ctx:left/ctx:right → ctx:bottom`)。追補では「C1 restrictsTo C2 と書くのは、C1 の観測領域の中に C2 の観測領域へ入り込む/共有面として現れる証拠(共有 adapter、共通境界、呼び出し先の合流点)を読んだとき」という手掛かり集+良悪対例を与える。正準の向きの一文定義は fixture 群と ag_measurement の解釈に突き合わせて確定する(§6 未決事項)。
- **cover 選択規準**: 「この cover で何を測りたいか(どの LawPolicy / MeasurementProfile の測定面か)」を cover の `label` と authoring note に書き、cover 1 個 = 測定面 1 個の対応を守る。context の重なり(共有 atom / restrictsTo 合流)が無い cover は Čech 系計測で退化することを良悪対例で示す。

### 3.5 SKILL.md の新 Authoring Workflow(9 段階)

1. **Preflight**: binary 解決(`ARCHSIG_BIN` → PATH → bundle 近傍 → checkout。無ければ停止して質問)。git revision / dirty を取得。ユーザーとスコープ(include/exclude/追加証拠)を確定。
2. **Scope manifest**: `archsig scope-manifest` を実行し、exclusions(private / generated 等)をユーザーに提示して承認を得る。承認前に読解を始めない。
3. **Pass A survey**: worklist を固定幅(既定 20 行)の連続 chunk に決定的分割し、chunk ごとに sub-agent が読解して candidate packet(pass-a)を返す。sub-agent は担当 chunk の全行に surveyRow を書く。既知 gap 類型を survey surface に明示: **per-file の semantic 走査(全ファイルで surveyedKinds に semantic を含める)/ 供給された runtime trace / 供給された permission・authority 証拠**。**スコープ round-trip 規則**: 読解中に「この source はスコープ外だ」と判明しても、sub-agent は skip しない(skip 理由に out-of-scope は存在しない)。integrator に報告し、integrator は scope manifest の exclusions 更新+ユーザー再承認(段階2 へ round-trip)を経て worklist を再生成する。スコープ判断は pass 実行中に分散させない(§5.2 の一括払い。extraction-protocol.md に手順として記載)。
4. **Pass B survey**: 別系統の sub-agent が、pass A の candidate を**共有せずに**同じ worklist・同じ chunk 割りで独立に読解する(走査順は共有し、読みは独立)。round-trip 規則は pass A と同一。
5. **Consistency**: `archsig extraction-diff` で突合。`onlyInPassA/B` の各項目について、integrator が**該当 source を再読解して**採否を `adjudications` に記録する。多数決や機械マージで裁定しない。
6. **Integrate**: 最終 `archmap.json` を組む。dedup は atom-match-key@1、refs は和集合(ただし key 一致・refs 相違の semantic 対は integrator 確認後に確定。§3.4)、subject / id は vocabulary-catalog の規約に正規化。alias 保存規律を適用。contexts / covers は mapping-guide の規準で選び、consistency の contextDiff の裁定を反映。
7. **Coverage ledger**: surveyRows から `coverage-ledger.json` を生成。rows は worklist と 1:1。`not_surveyed` / `partially_surveyed` 行に手続き理由を付す。
8. **Validate**: `archsig archmap` を authoring フラグ付きで実行。監査 check の不通過は修理して再実行(complete-first)。LawPolicy があれば `archsig analyze` を回し、coverage blocker を authoring 修理キューとして消化(従来どおり)。
9. **Deliver(Output Shape)**: 報告は次の順で固定 — (1) ArchMap path と `AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE` 等の監査結論、(2) scope 要約(revision、worklist 行数、exclusions)、(3) atoms の kind 別集計と代表例、(4) contexts / covers 要約、(5) consistency 要約(matchRate と裁定件数。数値は記録であり合否ではないと一行添える)、(6) coverage ledger の not_surveyed 行(理由付き、末尾)、(7) authoring artifact 一式のパス、(8) optional な analyze 結果。

**停止条件(明文列挙)**: binary 無し → 検証未実施と報告し ad hoc checker で代替しない / スコープ未承認 → 停止 / worklist 中に読めない source(権限等)→ surveyRow に手続き理由(private 等)を記録して続行(内容を推測・補完しない)/ スコープ外と判明した source → round-trip(段階3)。ユーザー再承認が得られるまで当該 source の裁定を保留 / LawPolicy 無しで analyze を頼まれた → law-policy-creater を指して停止。

**運用モード(コスト制御)**:

- `full-dual`(既定・初回作成と大規模改版): 全 worklist を二重抽出。
- `incremental-dual`: `--baseline` 増分 manifest の変更 source のみ二重抽出し、既存 ArchMap に統合。
- `single-pass`(ユーザーが明示選択した場合のみ): consistency は縮退形で記録。SKILL は既定で single-pass を選ばない。

### 3.6 検証: lint 連携と golden corpus 回帰(2 層)

**層1 — CI(cargo test)で lock する機械層**:

- `archsig scope-manifest` の決定性: fixture ツリー(下記 corpus)→ 期待 worklist のビット一致。**golden 比較は `worklist` / `exclusions` / `scopeSpec` 部分に限定**する。`repository.revision` / `dirty` は corpus が親リポ内にあるため親リポの状態で変わり、`id` は日付を含むので、テスト専用フラグ(`--revision-override` / `--id-override`)で固定値を注入するか、比較時にマスクする(どちらを採るかは M2 実装時に決めるが、仕様としてどちらかを必須にする)。
- `archsig extraction-diff` の突合: fixture candidate packets(pass A/B の手書き対)→ 期待 consistency(matched / onlyIn / matchRate。matchRate は §3.2(3) の定義式で期待値を固定)。判定語を含む候補 packet が fail する負系、object の無い semantic 候補が fail する負系。
- `archsig archmap` authoring 監査: 監査 5 check の positive / negative(worklist 未張り ledger・余剰行 ledger、provenance の無い atom、read 前 cite、grounding source の免除規則等)。
- **vocabulary-catalog 突合 lint**: カタログの axis 表・axis × predicate 対応表(機械可読の抜粋を fixture 化)と `ag_measurement.rs` の実フィルタ文字列を突合する test を置き、カタログと評価器の乖離を CI で lock する(§3.4)。
- 既存 golden corpus 慣行(per-evaluator executable lock)と同形式で `docs/tool/golden_corpus.md` に追記する。

**層2 — 抽出 golden corpus(agent 実行の回帰。CI 非ブロッキング)**:

- `tools/archsig/tests/fixtures/extraction_corpus/<corpus-repo>/` に sanitized なミニリポジトリ(20〜40 ファイル程度の教材ツリー: handler / repository / provider / permission check / docs / trace を含み、9 kind と alias 例・restrictsTo 例が全部現れるよう設計)を新設し、`expected/` に scope-manifest(worklist / exclusions 部分)/ atom-match-key 集合(kind 別)/ coverage-ledger を凍結する。
- 回帰手順(SKILL の Maintainer Validation 節に記載): corpus repo に対して SKILL を full-dual で実行し、`archsig extraction-diff --pass-a <今回の統合結果を packet 形式に射影したもの> --pass-b expected/atom-keys.json` で期待集合との差分レポートを取る。maintainer が差分を読み、期待集合の更新か SKILL 文面の修理かを判断する。実行記録は docs/tool の validation ノート(improvement PRD validation の前例に倣う)として残す。
- これが W1 への回答: 「リポジトリ → ArchMap」の品質を測る計器が初めて corpus として存在するようになる。**期待集合との一致は再現性の計測であって、現実リポジトリでの extraction completeness の証明ではない**(corpus の内側の bounded claim)。

---

## 4. 境界規律との整合

- **抽出と判定の分離(観測純化 PRD との整合)**: 新 artifact のどこにも判定語は現れない。統制語彙はすべて手続き記録(`read / partial / skipped`、`surveyed / not_surveyed`、`matched / onlyIn*`、`adopted / merged / not-adopted`)。さらに extraction-diff が候補段階で R3 lint を前倒し適用するため、判定語の混入は統合前に機械的に止まる。coverage ledger の「走査したが atom を観測しなかった」は authoring 手続きの記録であり、世界についての measured absence ではない(ArchMap 本体には入らない。欠落証拠の扱いは従来どおり ArchSig の `blocked / unknown / unmeasured`)。
- **semantic 機械化の禁止(purity PRD の却下条件)**: 機械層が行うのは列挙・ハッシュ・字面正規化・突合・参照整合だけで、atom の生成・採否・意味付けは常に読解判断。二重抽出の裁定も「再読解して決める」手続きであり、多数決・類似度マージ・自動採択を明示的に禁止する。一致検査は**見落としの検出装置**であって**読みの正しさの判定装置ではない**(unmatched の semantic atom は誤りの証拠ではなく再読解のキュー)。責務憲章 原則2(観測の主観は機能)を侵さない。
- **境界の一括払い(AGENTS.md:65-67)との整合**: 本設計は観測の質の問題を観測層(SKILL + authoring artifact)で解決し、ArchSig の計測経路には観測ヘッジ・補完・fallback を一切足さない。`analyze` は authoring artifact を読まず、挙動不変。authoring 監査は `archsig archmap`(観測層向けの契約検査。既存の schema / refs 検査と同種)に閉じる。observationGaps / confidence 類を ArchMap schema に戻さない(v0 への逆行禁止)。**スコープ判断も一括払いの対象**: スコープの選択と変更は scope manifest の承認ゲート(ユーザー + author)に一括し、pass 実行中の sub-agent / integrator に out-of-scope 判断を分散させない(§3.2(2)・§3.5 段階3 の round-trip 規則)。
- **bounded claim(extraction completeness を主張しない)**: coverage ledger の主張は「記録された revision における、選択スコープ内の走査記録」まで。claimBoundary は定数 1 文で、non-conclusion 一覧を持たない。監査の肯定的結論(`AUTHORING_SURVEY_TRACEABLE_WITHIN_SCOPE`)を先頭に置き、not_surveyed 行は理由付きで末尾に置く(主役化しない)。
- **doctrine 固定との整合**: 語彙カタログは doctrine 内の recommended token 表であり、著者に語彙体系の選択・拡張の裁量を与えない(適用の主観は守る)。カタログ外 **predicate** トークンの採用は integrator の裁定記録を要件とし、裁定は語彙体系の変更ではなく「この観測に既存トークンが当てはまらなかった」という適用判断として記録される。**新 axis の導入はこの適用判断の範囲外**であり、authoring run 内では行わず、doctrine / registry 側の変更(§3.4、§6.3)へ escalation する。観測層の役者(author / sub-agent / integrator)は語彙体系を選ばない・名乗らない・拡張しない(観測純化 PRD 原則3、責務憲章 原則3)。
- **ウィトゲンシュタイン的停止**: 読めない・与えられていない証拠は推測せず、exclusions / notes に理由記録して沈黙する。停止条件は SKILL に明文列挙(既存慣行の踏襲)。

---

## 5. 移行とリスク

### 5.1 移行段階

| 段階 | 内容 | 依存 |
| --- | --- | --- |
| M1 | references 増補と prompt-pack の candidate packet schema 化(binary 変更なし。scope manifest / ledger は手書き運用で先行) | なし。即着手可 |
| M2 | CLI 3 面(`scope-manifest` / `extraction-diff` / `archmap` 監査フラグ)+ 新 4 schema の serde 型 + 層1 golden lock(vocabulary-catalog 突合 lint 含む)+ 新規依存 3 crate の追加 | M1 の schema 確定 |
| M3 | extraction corpus(教材ミニリポ + expected)新設と Maintainer Validation 手順の整備・初回実測 | M2 |
| M4 | reader / pr-reviewer の v2 化と接続(complete-first ループを v2 で閉じる。`--baseline` 増分 manifest を CI/PR 経路へ)| 別設計次元(レガシー破棄・artifact 再設計)と同時進行 |

### 5.2 リスクと手当て

| リスク | 手当て |
| --- | --- |
| 二重抽出でコスト約 2 倍 | 運用モード 3 種(§3.5)。増分更新は変更 source のみ dual。single-pass は縮退形として正直に記録 |
| 決定的走査が読解の自由を縛る | 縛るのは「全 worklist 行を最低 1 回読む」ことと chunk 割りだけ。読解の深さ・往復・chunk 外参照は自由。chunk 境界で context が分断される問題は examples の悪例+integrator の統合責務で扱う |
| 機械化が semantic の判定化へ滑る | 機械層の許容 4 操作(列挙・ハッシュ・突合・参照整合)を SKILL に明文列挙し、それ以外の機械操作を禁止。extraction-diff は候補の内容を解釈しない(キー字面のみ) |
| matchRate の閾値 verdict 化の誘惑 | 閾値を仕様に置かない。SKILL は裁定手続きのみ課す。報告文面にも「記録であり合否ではない」定型を置く |
| scope spec 自体の主観・恣意 | include/exclude はユーザー承認ゲートを必須化し、scope manifest に `approvedBy` を記録。スコープの選択は観測者境界の一部としてユーザー + author が一括して負う。pass 実行中のスコープ判断は round-trip 規則で承認ゲートへ回送(§3.5 段階3) |
| authoring artifact の管理負担 | 置き場所を `authoring/` 配下に規約化し、run 出力(out-dir)とは分離。CI 連携次元で run manifest から参照する形は artifact 再設計側と調整 |
| 新 CLI が計測経路と混同される | docs/tool 側で「authoring 支援 3 面は観測層の契約検査であり、measurement packet に一切寄与しない」と 1 節で明記(schema-catalog にも authoring 系として登録) |
| カタログが評価器と乖離し計測入力を退化させる | axis 表・axis × predicate 対応表は ag_measurement.rs の実フィルタから機械採録し、層1 の突合 lint で乖離を CI 検出(§3.4・§3.6) |

---

## 6. 未決事項

1. **archmap/v2 本体に revision を持たせるか**: 現設計では鮮度は scope manifest 側の記録に置いた(ArchMap schema 不変)。CI / PR レビュー(pr-review の AG 後継)で ArchMap 単体の自己記述性が要るなら、top-level `sourceRevisionRef` 1 フィールドの追加が候補。artifact 再設計次元と調整して決める。
2. **restrictsTo の正準方向の一文定義**: fixture 実測(包含側 → 共有側)に基づく手掛かり集までは本設計で書けるが、正準定義は ag_measurement の解釈・第IV部の cover 語彙と突き合わせて確定する。
3. **vocabulary-catalog を機械可読にするか**: 初版は references 文書+層1 突合 lint 用の機械可読抜粋(fixture)に留める(closed enum 化しない)。将来、lint の「カタログ外トークンの warning(fail ではない)」を registry manifest 側に持つかは、LawPolicy 再設計次元の registry 分離方針と合わせて判断。**新 axis 導入の escalation(§3.4)の受け皿もこの registry manifest 方針に置く**(axis 表の変更 = doctrine / registry 側の版数上げとして扱う)。
4. **二重抽出の既定深度**: full-dual を既定にしたが、大規模リポジトリ(worklist 数百行超)では「semantic / authority / contract の 3 kind だけ dual、component / relation は single + 監査」のような kind 別サンプリングも候補。extraction corpus の初回実測(M3)で決める。
5. **extraction corpus の題材**: 新規作成する教材ミニリポの内容(言語、ドメイン、alias 例の作り込み)。既存の practical-rust-service example を種にするか、別ドメイン(注文/在庫系)で作るか。
6. **skill 名の綴り**: `creater` は既存トリガー資産として本設計では継続。レガシー破棄次元で skills を大改稿する際に `archmap-author` 等への改名を再検討してよい(改名する場合は agents/openai.yaml と docs の同時更新)。
7. **candidate packet の保存期間**: provenance closure の監査は packet の現存を前提とする。納品物に含めて恒久保存するか、consistency + ledger への要約で足りるとするか(CI 連携の artifact 保持方針と合わせて決める)。
8. **NFC 依存の縮退案**: atom-match-key@1 の正規化を「trim + Unicode コードポイント同一」に緩めれば `unicode-normalization` 依存を落とせる。初版は NFC を採る(subject に非 ASCII 識別子が入る場合の突合安定性を優先)が、依存最小方針を強く優先する場合の縮退先として記録する。

---

## 査読対応

各指摘の採否と対応箇所。

1. **[boundary/minor] 新 axis の発明を integrator 裁定で許す自己矛盾 — 採用**。§3.4 を提案どおり書き換えた: カタログ外 predicate トークンの使用は「既存トークンが当てはまらなかった」適用判断として integrator 裁定記録を要件とし(従来どおり)、**新 axis の導入は authoring run 内の裁定事項とせず、doctrine / registry 側の変更(§6.3 の registry manifest 方針、LawPolicy 再設計次元)への escalation** とした。§4 の doctrine 固定段落にも同じ区別を明記し、§6.3 に escalation の受け皿を追記した。axis は AG 計測が読む構造的セレクタであり predicate より規律上重い、という指摘の根拠もそのまま §3.4 に採り入れた。
2. **[boundary/minor] out-of-scope skip によるスコープ判断の分散 — 採用**。surveyRows(§3.2(2))と coverage ledger(§3.2(4))の理由語彙から `out-of-scope` を外し、手続き理由(`private | binary | unreadable | tooling-error`)に限定した。読解中にスコープ外と判明した source は skip せず、scope manifest の exclusions 更新+ユーザー再承認へ round-trip する規則を §3.5 段階3 に置き、extraction-protocol.md への記載を指定した。`out-of-scope` は exclusions(スコープ確定・再承認時)の語彙としてのみ残る。§3.2(4) の例示行を worklist 内の手続き skip(private)に差し替え、§4 の一括払い段落と §5.2 にスコープ判断の一括を追記した。
3. **[theory/minor] W4 の「context の atom 族を経由して H^1 を直接変える」は計測経路と不一致 — 採用**。コードで確認した(`cech_edges` は cover 選択 contexts・restrictsTo・`axis=="cech" && predicate=="sectionValue"` atom の object 字面しか読まず、contexts[].atoms は不参照。ag_measurement.rs:9622-9694)。W4 の帰結欄を提案どおり二段に書き分けた: (直接)sectionValue の object 字面揺れが cech mismatch 計算に効く、(間接)capability 系 predicate の揺れは dedup 残留・context/cover の切り方を通じて波及する。
4. **[theory/minor] vocabulary-catalog 初版案の axis/predicate カテゴリ混同 — 採用**。`support` を axis 表から外し(生値 predicate として `square-free` / `section-factorization` axis と組で収録)、axis 表は ag_measurement.rs の実フィルタから機械採録する方針を明記した。「どの axis 上のどの predicate を AG 経路が読むか」の axis × predicate 対応表を §3.4 に新設し、カテゴリ混同を構造的に防ぐ形にした。
5. **[feasibility/major] axis recommended list が実コード・fixture と乖離 — 実質採用(一部事実訂正付き)**。axis 表を実フィルタ値(`cech / square-free / section-factorization / tor / transfer / period / laplacian / witness / boundary-residue / restriction-compatibility` に加え、grep で確認した `coherence`(ag_measurement.rs:9874)と `refactor`(:2937))+ fixture 実測の記述用 axis から機械採録する方針に改め、AG 消費 axis と記述用 axis を別列で区別した。M2 層1 に「カタログ収録 axis × 評価器フィルタ値の突合 lint」を追加した(§3.6、§5.1、§5.2)。**事実訂正**: 指摘中の「`semantic` は atom kind であって fixture に axis として出現しない」は不正確で、fixture 実測では `"axis": "semantic"` が 3 件出現する(ほかに relation / capability / effect / authority 等の kind 鏡映 axis も出現)。ただし指摘の実質(初版リストが AG 消費 axis と乖離し、従うと計測入力が退化する)は正しいため、これらは「記述用 axis(AG 経路は読まない)」の列として明示収録する形で反映した。
6. **[feasibility/major] `authoring-sources-resolve` が現行 sources 慣行(grounding キー)と矛盾 — 採用**。§3.3c に解決規則 4 項を明文化した: src: の worklist 直接一致、doc: の path 部解決、trace: 等 authorAdded 直接一致、grounding sources(`ctx:*` / `kind: "policy"` エントリ)の kind ベース免除リスト。sourceId 規約の記述は「現行慣行の規約化」から「現行慣行の変更(短縮ラベル → repo 相対 path)」に改め、既存 fixture は authoring フラグを与えない限り監査されないため互換問題を生じないことを §3.2(1) に一行明記した。
7. **[feasibility/major] atom-match-key@1 の機械 dedup が alias 保存規律と衝突 — 採用(提案 (a) を主、(c) を安全網、(b) は不採用)**。(a) semantic kind の object 必須規約を vocabulary-catalog(§3.4)に置き、candidate packet 段階の lint(§3.3b)で機械裏付けする形を採った。本文の「意味の異なる atom は潰れない」という無条件主張は「意味差がキー担持フィールドに載っている場合に限る」と成立条件付きに修正した(§3.4 mapping-guide)。さらに (c) を縮小採用: key 完全一致・refs 相違の semantic 対の refs 和集合統合は機械で確定せず integrator が意味の同一性を確認して確定する(§3.4・§3.5 段階6)。(b)(semantic に限り refs をキーに含める)は不採用: pass A/B は同一 source でも行参照が揺れるため、refs をキーに入れると pass 間突合(意味的同一の match)が systematically 壊れ、extraction-diff の目的と矛盾する。現行 repository-survey.md の dedup キーが refs を含むのは単一 pass 内の規律であり、pass 間突合キーにはそのまま持ち込めない。
8. **[feasibility/minor] ledger の out-of-scope 行が `authoring-ledger-spans-worklist` と両立しない — 採用**。ledger の rows を worklist と 1:1 に統一し(余剰行も欠落行も fail と check 内容欄に明記)、スコープ外の記録は scope manifest の exclusions への一本化とした。例示行を worklist 内の手続き skip(private)に差し替え、worklist 内 skip の理由語彙と exclusions の語彙を別表として定義し直した(指摘2 と一体で対応)。
9. **[feasibility/minor] authorAdded 証拠の投入機構が未定義 — 採用**。`archsig scope-manifest --add-evidence <kind>:<name>=<repo相対path>` フラグを仕様化し(§3.2(1)・§3.3a)、証拠は必ずファイルとして供給、contentHash はそのファイル内容の sha256、path はその repo 相対 path(例の `path: null` を修正)とした。`--add-evidence` は `scopeSpec.addedEvidence` として manifest に記録され、再実行・`--baseline` 増分でも保持・再現されることを明記した。
10. **[feasibility/minor] 新規依存とパス解決の無言追加 — 採用**。§3.3 冒頭に新規依存 3 crate(sha2 / unicode-normalization / globset)と現行 4 依存との対比、glob 引数の binary 内展開を明記した。NFC を避ける縮退案(trim + コードポイント同一)を §6.8 として追加した。
11. **[feasibility/minor] golden lock の非決定フィールドと matchRate の算術不整合 — 採用**。§3.6 層1 で golden 比較を worklist / exclusions / scopeSpec 部分に限定し、revision / dirty / id はテスト専用フラグでの注入またはマスクを仕様化した。matchRate の定義式 `matched / (matched + |onlyInPassA| + |onlyInPassB|)` を atom-match-key@1 仕様に併記し、§3.2(3) の例を 0.992(= 132/133)に修正した。
12. **[feasibility/minor] repository-survey.md の行方が未記載 — 採用**。§3.4 の references 構成に「repository-survey.md は extraction-protocol.md に吸収して削除。survey surface の目安リストと W8 の gap 類型は extraction-protocol.md『Survey surface(走査面の目安と既知 gap 類型)』節へ移設」と明記した。
