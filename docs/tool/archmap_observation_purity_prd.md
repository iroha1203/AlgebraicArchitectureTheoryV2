# ArchMap 観測純化 PRD

対象は v0.4.0 の ArchMap v2 入力契約と、それを消費する ArchSig の AG measurement 軸
(`cech` / `square-free` / `section-factorization` / `boundary-residue` / `transfer` ほか)。
本 PRD は「ArchMap には観測だけを生のまま書き、判定は ArchSig が計算する」という境界を、
schema・validation・AG measurement パス・authoring 規律の四面で回復する。

関連: [責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md)(なぜこの分割かの理論的根拠)、
[ArchMap 最小観測契約 PRD](archmap_minimal_observation_contract_prd.md)(v0→v1 の Removed Fields)、
[guideline.md](guideline.md) / [README.md](README.md)(現行 boundary statement)。

## 問い

**ArchMap から「判定の主観」を排しきれるか —— 観測の主観(とくに semantic atom の意味読み取り)は一切痩せさせずに。**

この問いを採否の判定規律として使う。各改修・各受け入れ条件は、次の二面の両方を満たすときだけ採用する。

- **(採用条件)** それは ArchMap から「判定の主観」を減らすか。
  判定の主観とは、(a) あるべきと照らした評価語(`mismatch` / `violation` / `obstruction` / `risk` / `nonzero` …)、
  (b) どの語彙体系で観測するかの選択裁量(doctrine)、(c) ArchSig がやるべき計算結果の先書き(minimal support / certificate / dimension …)を指す。
- **(却下条件)** それは「観測の主観」を機械判定化または減縮しないか。
  観測の主観とは、観測者が source を読んで下す主観的な意味読み取り、とくに semantic atom の `meaning` 自由記述を指す。
  これを keyword lint・正規化・heuristic 生成などで機械化する改修は、この問いに照らして**却下**する。
  semantic を機械判定化したら、ArchMap は静的解析に堕ち、AAT の上に計算を載せる土台が消える。

## Core Thesis

ArchMap は「世界がこうなっている」だけを生のまま書く**観測契約**である。
「あるべきと照らしてどうか」は ArchMap × LawPolicy → ArchSig の**計算**でしか生まれない。

現状の AG measurement 軸は、この境界を三段階で破っている。

1. **局所判定の先取り** —— 観測者が「この二つの context は overlap で食い違う(`mismatch`)」「この関係は obstruction generator だ」と評価を書き、ArchSig はそれを数えるだけになっている。
2. **計算結果の先書き** —— 観測者が `minimalForbiddenSupports=…` や `nsdepth=2` といった ArchSig が計算すべき代数的成果物を ArchMap に貼り付け、ArchSig はそれを照合するだけになっている。
3. **規律と実装の衝突** —— ArchMap authoring 規律(SKILL / prompt-pack / mapping-guide)は `mismatch` / `obstruction` を禁止語として挙げているのに、AG measurement パスはまさにその語を `predicate` として要求している。しかも禁止はコードで強制されておらず、文書上の努力目標にとどまる。

本 PRD はこの三段階を塞ぎ、観測者の責任を「正しく見たか」だけに限定する。

## 現状診断(証拠)

記載の行番号は本 PRD 執筆時点のもの。実装時に再確認する。

### 判定の先取り(cech / square-free)

`tools/archsig/tests/fixtures/ag_measurement/archmap_v2_cech_h1_visible.json` の cech atom:

```json
{ "id": "atom:left-bottom-cech-mismatch", "kind": "relation",
  "subject": "ctx:left", "object": "ctx:bottom",
  "axis": "cech", "predicate": "mismatch",
  "refs": ["ctx:left", "ctx:bottom", "src:cover"] }
```

観測者が「left と bottom は overlap で食い違う」という**比較結果=判定**を、atom id と `predicate` の両方に書いている。
ArchSig(`tools/archsig/src/ag_measurement.rs` の `cech_edges()` 周辺、`predicate ∈ ["mismatch","cechMismatch","residue"]` で filter)は、この marker を数えて `e_ij = (該当数) mod 2` を出すだけ。
**H1 計算の比較は観測者がやっており、ArchSig は集計しているにすぎない。**

`archmap_v2_square_free_repair.json`:

```json
{ "id": "atom:ob-checkout-inventory", "axis": "square-free",
  "predicate": "obstructionGenerator", "subject": "x_checkout", "object": "x_inventory", ... }
```

観測者が「どの関係が obstruction generator か」を**選別**して書く。obstruction かどうかは law と計算で決まるべきもので、観測ではない。

### 計算結果の先書き(square-free certificate)— 最も重い侵犯

同 fixture の certificate atom:

```json
{ "id": "atom:nsdepth-certificate", "kind": "semantic", "axis": "square-free",
  "predicate": "nsdepthCertificate",
  "object": "nsdepth=2;depthRule=alexanderDualMaxMinimalHittingSet@1;minimalForbiddenSupports=x_checkout+x_inventory|x_inventory+x_payment;supportAtomRefs=…" }
```

`minimalForbiddenSupports` も `nsdepth` も、ArchSig が enumeration で**計算すべき**代数的成果物である。
現状はそれを観測者が先に書き、ArchSig が「観測者の計算と自分の計算が一致するか」を照合する構造になっている。
これは観測ではなく、観測者が ArchSig の仕事を代行している。

### 規律と実装の衝突、未強制の禁止

- `tools/archsig/skills/archmap-creater/SKILL.md:48-52` は `mismatch` / `obstruction` / `violation` … を禁止語として挙げ、「ただし extraction doctrine / fixture vocabulary が明示的に要求する場合のみ可」という例外条項を持つ。
- AG measurement パスは `predicate: "mismatch"` / `"obstructionGenerator"` を**要求する**。つまり例外条項が AG 軸全体を例外化し、禁止を空文化している。
- `tools/archsig/src/archmap.rs` の v2 検証エントリ `validate_archmap_v2_report()`(line 42-)が持つ checks ベクトルに、判定語 atom を拒否する validation は**存在しない**。`atom:service-violation` のような id も `predicate:"violatesLaw"` も現状では通る。禁止は文書だけの努力目標。

### doctrine は計算に効いている(provenance ではない)

- `tools/archsig/src/schema/archmap.rs` の `ArchMapDocumentV2` で `extraction_doctrine_ref` は `#[serde(default)]` を持たず **required**。
- `compare_archmap_v2_doctrine()`(`archmap.rs:21-40` 付近)が doctrine fingerprint 不一致を `cross_doctrine_not_comparable` として**拒否**する(公理 A8 Essential Uniqueness の tool 実装、`archsig_v0_4_0_algebraic_geometry_measurement_prd.md` R12)。
- すなわち doctrine 廃止はタダではなく、A8 比較ロジックに触れる。後述 R1 で正面から扱う。

## Design Principles

### 1. 観測と判定の分離は絶対

ArchMap の atom は "X is the case"(こうなっている)だけを書く。
"X is good / bad / violation / mismatch / nonzero"(あるべきと照らした評価)は一語も書かない。
後者は必ず ArchMap × LawPolicy → ArchSig の計算でのみ生まれる。

### 2. 主観には二種類ある。守るものと排するものを取り違えない(哲学的根拠は[責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md)原則2)

- **観測の主観**(守る): 観測者が source を読んで下す意味の読み取り。とくに semantic atom の `meaning`。機械判定化したら静的解析と区別がつかなくなる。これは AAT の核であり、バグではなく機能である。
- **判定の主観**(排する): あるべき評価、語彙体系の選択裁量(doctrine)、計算結果の先書き。

### 3. doctrine は固定し、観測者から裁量を奪う

公理 A8(Essential Uniqueness, AAT 第I部)が述べるのは、source と extraction doctrine `(V, Γ, R, ρ, E, N)` の各ペアに対して canonical Atom family が一意である、という**相対化された条件付き一意性**である。A8 は複数 doctrine の共存を排除せず、doctrine の固定を要求もしない。
したがって doctrine を単一に固定することは A8 の**要件ではなく**、A8 に相対化された**実務 tool の設計選択**である。本 PRD はその選択を、観測者の責任最小化のために採る。
理論本文では doctrine `(V, Γ, R, ρ, E, N)` を多 doctrine を許す一般論のまま残す(健全性のため書き換えない)。実務 tool ではその一特殊化として、doctrine を**焼き付けた一個の固定定数**とし、観測者は doctrine を選ばない・名乗らない・拡張しない。
語彙体系は AAT 由来で固定され、観測者は固定された言語ゲームの中で主観的に意味を読むだけになる。

### 4. 計算入力は生値。比較・選別・最小化はすべて ArchSig

ArchMap は per-context の生の section データ・生の関係・生の support を書く。
二値の比較(cech defect)、obstruction の選別、minimal support の計算、certificate の生成は、すべて ArchSig が行う。
「禁止か否か(forbidden-ness)」は観測ではなく**法**であり、LawPolicy / MeasurementProfile 側の責務とする。

### 5. 判定語の禁止はコードで強制する

文書上の努力目標を、validation の hard error に昇格する。
ただし AG measurement パスが判定語を要求している間は強制できない。順序は R2(AG パスを中立 atom 消費へ改修)→ R3(禁止の hard-error 化)とする。

### 6. semantic の意味読み取りは保護する

`meaning` 自由記述、`is_promoted_truth_status` の昇格ガード、normalizer の binding-through(`diagram`/`meaning` を加工せず素通し)は維持する。
semantic atom に keyword lint / 正規化 / heuristic 生成を導入しない。

## Responsibility Split

| Layer | 所有する(書く/決める) | 委譲する |
| --- | --- | --- |
| **ArchMap(観測層)** | source 由来の生の atom(component / relation / capability / effect / contract / authority / runtime / semantic)、per-context の生 section 値、生の関係・support、contexts、covers | doctrine の選択(→ 固定定数)、比較・選別・最小化・certificate(→ ArchSig)、forbidden-ness(→ LawPolicy) |
| **LawPolicy(制度選択層)** | policy pack / evaluator / basis / scope / severity、何が forbidden か(law universe)、witness family / coefficient / cover の選択(MeasurementProfile) | witness predicate・signature axis・score formula の手書き(→ evaluator registry) |
| **ArchSig(計算層)** | cech defect の比較、minimal forbidden support の enumeration、obstruction ideal、H^n / Tor / rank / certificate、structuralVerdict、bounded diagnostic conclusion | source の再読、入力 contract の補完・推測・拡張(行わない) |

## 改修(本体)

### R1: doctrine を「観測者の入力」から「固定定数」へ格下げ

- `extractionDoctrineRef` を ArchMap v2 の author 入力から外す。語彙(V)・use-rule(R)・normalization(N)は AAT 由来の固定セットとして ArchSig に内蔵する。
- 関連実装(本 PRD 執筆時点の位置、要再確認):
  - `tools/archsig/src/schema/archmap.rs` `ArchMapDocumentV2` / `NormalizedArchMapV2` / `NormalizedArchMapSummaryV2` から doctrine フィールドを除去または固定化。
  - `tools/archsig/src/archmap.rs` `check_archmap_v2_doctrine()` を削除、`check_archmap_v2_atom_kind_vocabulary()` を固定語彙照合へ。
  - `compare_archmap_v2_doctrine()`(`archmap.rs:21`)の fingerprint 比較ロジックを削除し常に comparable とする。A8 cross-doctrine 比較は単一ツール配備では退化する(後述 Non-Goals)。
  - `tools/archsig/src/normalizer.rs` / `ag_measurement.rs` の doctrine fingerprint 伝播を固定値へ。
  - fixtures(`archmap_v2*.json`, `tools/archview/examples/**`)から `extractionDoctrineRef` を除去または静的化。
- atom の `kind` 語彙の検証は維持する(未知 kind は hard error のまま)。変わるのは「語彙を観測者が選ぶ」点だけ。
- **採用戦略(推奨: フィールド除去)**: `extraction_doctrine_ref` を schema から削除する案を第一とする。代替として、フィールドを残し固定 canonical 値(例 `doctrine:aat-canonical@1`)以外を validation で拒否する hardcode 戦略も可。どちらを採るかは v1 互換・migration 容易性で実装時に決める。いずれの場合も観測者は doctrine を自由設定できない。

### R2: 計算入力の生値化(AG measurement 軸)

軸ごとに「観測者が書くもの」を生データへ還元し、比較・選別・最小化・certificate を ArchSig へ移す。
具体的な field 名・schema 形は実装(prd-loop)が field 設計レビューで確定する。下表は各軸で「廃止する評価表現」「観測者が代わりに書く生データ」「中立 predicate 候補」を定める。候補名は確定仕様ではなく、評価を含まない命名であることが要件。

| 軸 | 廃止する評価表現 | 観測者が書く生データ | 中立 predicate 候補 |
| --- | --- | --- | --- |
| cech (H1) | `predicate:"mismatch"`、`*-mismatch` id | 各 context が overlap 上で section に割り当てる生の値 | `sectionValue` |
| square-free | `predicate:"obstructionGenerator"` | co-occur する変数・atom の生の関係 | `support` / `cooccurrence` |
| section-factorization | `predicate:"obstructionGenerator"` | 同上(生の support) | `support` |
| square-free certificate | `nsdepthCertificate` / `nsdepthMonotoneScope` の計算済み `object` | (何も書かない。raw support のみ) | (廃止) |
| boundary-residue | 評価を含む `predicate` 名があれば | per-context の生の restriction 値 | 中立名(実装時に入力 audit) |
| transfer | 同上 | `groundCost` 等の生の数値はそのまま可 | 既存が中立なら維持 |

軸ごとの要点:

- **cech(H1)**: 観測者は「mismatch」と言わない。overlap 上の生の section 値を書き、二値の比較(defect `e_ij`)は ArchSig が計算する。`cech_edges()`(`ag_measurement.rs:9994`、現在 `predicate ∈ {"mismatch","cechMismatch","residue"}` で filter)を、predicate を数える方式から生 section 値を比較する方式へ改修する。
- **square-free / section-factorization**: 観測者は生の関係・support を中立 predicate で書く。`square_free_generators()`(`ag_measurement.rs:9413`)/ `section_forbidden_supports()`(`:8794`)の `obstructionGenerator` filter を中立 axis ベースへ。「どの support が forbidden か」は **LawPolicy / MeasurementProfile の law universe** が選ぶ(第III部:law は loci を切り出す)。inclusion-minimal 列挙と obstruction ideal の構成は法理論では実行者未指定であり、本ツールでは ArchSig が担う実装分割とする。
- **square-free certificate(最優先)**: 計算済み成果物(`minimalForbiddenSupports=…` / `nsdepth=…`)の先書きを**廃止**し、certificate は ArchSig が計算・発行する。注意: 現状この atom は `kind=semantic` だが、それは正当な semantic 観測ではなく計算結果の先書きである。改修後は raw support を中立 atom で表し、certificate atom を ArchMap 入力から除く。判定は atom の構造(axis + 生 support)で識別し、predicate に頼らない。semantic 観測一般の保護(原則6)とは独立であり、巻き添えにしない。
- **boundary-residue / transfer**: 生の数値(`groundCost` の `2`、`transferPairing` の `support:api=0.25` など)は観測として許容。`predicate` 名が役割を超えて評価を含む場合のみ中立名へ。`boundary-residue` 内部の `boundary_residue_mismatch` は ArchSig の内部計算であって ArchMap 入力語彙ではない。boundary-residue の入力 atom は他軸より仕様化が薄いため、実装時に入力 atom の audit を行う。
- **代数アルゴリズム本体**(`edge_cochain_is_coboundary` の potential recovery、`matrix_rank_f2` による H2 次元、minimal support の subset enumeration)は**変えない**。変わるのは入力契約と、値を渡す手前の比較・選別段だけであり、コホモロジー / イデアル計算そのものは不変である。

### R3: 判定語の hard-error 化

- `tools/archsig/src/archmap.rs` に `check_archmap_v2_no_diagnostic_shortcuts()` を追加し、v2 検証エントリ `validate_archmap_v2_report()`(`:42`)の checks ベクトルに組み込む。
- atom の `id` と `predicate` が判定語に該当する場合は fail。検査は**確定した禁止語 whitelist による語境界 exact match**(導出形を含む)に限定し、substring / regex heuristic は使わない。判定対象は構造化フィールドである `id` と `predicate` のみで、**semantic atom の `meaning` 等の自由記述は validation 対象に含めない**(原則6 の semantic 保護を巻き込まないため)。
- 禁止語の初期集合: `mismatch` / `obstruction` / `violation` / `risk` / `debt` / `unsafe` / `lawful` / `nonzero` / `failure`。
- v1 側にも同等チェックを検討。
- **順序厳守**: R2 で AG パスが中立 atom を消費するよう改修した**後**に有効化する。先に有効化すると AG fixtures が壊れる。

### R4: authoring 規律と AG パスの整合

- SKILL.md:48-52 / prompt-pack.md:34-37 / mapping-guide.md:72-75 の**例外条項を削除**し、無条件禁止へ書き換える。doctrine 固定化(R1)後は fixture vocabulary も可変ではないため、「doctrine / fixture vocabulary が要求すれば可」という逃げ道は成立しない。
- 置換文言(主旨): 「ArchMap v2 では `mismatch` / `obstruction` / `violation` / `risk` / `debt` / `unsafe` / `lawful` / `nonzero` / `failure` 等の診断語を**無条件に禁止**する。これらは観測ではなく判定であり、何が forbidden / obstructive / violating かは ArchMap × LawPolicy → ArchSig の計算でのみ決まる。例外はない。」
- AG fixture が中立 atom 語彙(R2)に移行したことを規律文書へ反映する。
- 規律文書(skills)と schema validation(R3)が同一の禁止語原則を述べる状態にする。

## Changed / Removed Fields

| 対象 | 現状 | 改修後 |
| --- | --- | --- |
| `extractionDoctrineRef`(ArchMap v2) | author 必須入力、A8 比較に使用 | 除去/固定定数。語彙は ArchSig 内蔵 |
| cech `predicate:"mismatch"` | 観測者が比較結果を書く | 廃止。per-context の生 section 値を書き、defect は ArchSig 計算 |
| `predicate:"obstructionGenerator"` | 観測者が obstruction を選別 | 廃止。生関係を書き、forbidden は LawPolicy、minimal は ArchSig |
| `nsdepthCertificate` / `nsdepthMonotoneScope` の計算済み object | 観測者が certificate を先書き | 廃止。certificate は ArchSig が発行 |
| 判定語 id / predicate | validation 素通り | hard error(R3) |
| SKILL 例外条項 | doctrine 要求時に判定語可 | 削除(R4) |

## Failure Contract

- 判定語を含む atom id / predicate → validation fail(R3 有効化後)。
- AG 入力に計算済み certificate(`minimalForbiddenSupports=` 等)が現れる → validation fail。
- doctrine フィールドが author 入力に残っている → schema reject(R1 後)。
- 未知 atom `kind` → hard error(現状維持)。
- semantic atom の `diagram` / `meaning` 欠落 → 既存どおり normalization blocker(measured_zero ではない)。

## Implementation Plan

順序は依存関係に従う。**R2 → R3 は必須**(R3 を先に有効化すると、判定語を持つ既存 AG fixture が validation で壊れる)。**R1 と R2 は論理的に独立**で、schema breaking change の R1 を先に置く方が実装は安定する。

1. **R1**: doctrine 格下げ。schema・validation・normalizer・比較・fixtures・関連 docs/skills を固定語彙へ。A8 比較の退化を README/PRD に記録。
2. **R2**: AG measurement 軸の入力生値化。軸ごとに中立入力 schema を定義し、`ag_measurement.rs` の各 `*_edges` / `*_generators` / certificate 経路を「中立 atom を消費し ArchSig が比較・選別・最小化・certificate 発行」へ改修。golden fixtures を中立版へ更新。既存の代数アルゴリズム本体は不変。
3. **R3**: `check_archmap_v2_no_diagnostic_shortcuts()` を追加し有効化。negative fixtures を追加。
4. **R4**: skills の例外条項削除と AG 中立語彙の反映。
5. **検証**: `cargo test --manifest-path tools/archsig/Cargo.toml`、`analyze` の e2e、`git diff --check`、hidden Unicode scan。

## Acceptance Criteria

問いに照らして判定する。各条件は「判定の主観を減らすか」かつ「観測の主観を痩せさせないか」を満たすこと。

### ArchMap 観測純化
- ArchMap v2 のどの正規 fixture にも `predicate:"mismatch"` / `"obstructionGenerator"` / `nsdepthCertificate` の計算済み object が存在しない。
- 判定語を含む id / predicate が validation で hard error になる(negative fixture で確認)。
- `extractionDoctrineRef` が author 入力に存在しない、または固定定数として扱われる。

### 計算境界
- cech `e_ij`、minimal forbidden support、obstruction ideal、nsdepth certificate が、すべて ArchSig の計算出力であり、ArchMap 入力に先書きされていない。
- H1 potential recovery / H2 rank / minimal support enumeration の計算結果が、改修前後の同等シナリオで一致する(中立入力からの再計算で従来 verdict を再現)。
- 検証手順: 既存 golden fixture(`archmap_v2_cech_h1_visible.json` 等)を中立入力版へ書き換えた fixture を用意し、改修後コードでの `structuralVerdict` と computedInvariants(H1/H2 次元、minimal support)が、改修前の同シナリオの値と一致することを test で確認する。

### semantic 保護(却下条件のガード)
- semantic atom の `meaning` は自由記述のまま。keyword lint / 正規化 / heuristic 生成が**導入されていない**。
- `is_promoted_truth_status` 昇格ガードと normalizer binding-through が維持されている。
- semantic atom 欠落時は blocked であり measured_zero へ変換されない。

### 規律整合
- SKILL / prompt-pack / mapping-guide に判定語の例外条項が残っていない。
- 規律文書と `check_archmap_v2_no_diagnostic_shortcuts()` が同一の禁止語原則を述べる。

### 理論整合
- AAT 本文(`docs/aat/algebraic_geometric_theory/`)は一切変更しない。
- doctrine は理論本文では A8 の錨として残り、実務 tool では固定定数になる、という分界が README / 憲章に明記される。

## Non-Goals

- AAT 数学本文の改訂。doctrine も semantic も理論側では健全性のため残す。本 PRD は実務 tool 契約のみを扱う。
- multi-doctrine 比較の維持。単一固定 doctrine を前提とし、A8 の cross-doctrine 比較ロジック(compute 側)は退化させる(将来再導入する場合は別 Issue)。AAT 本文の A8 定理そのもの(theorem 側)は不変であり、単一方言化した tool は多方言理論の一特殊化にあたる——この対比は README に記録する。
- semantic atom の機械判定化・意味の自動分類(問いの却下条件により明示的に範囲外)。
- H1 / H2 / obstruction の代数アルゴリズム自体の変更。本 PRD は入力の出所と語彙のみを直す。
- 単一スコア化。Architecture Signature は多軸診断のまま。
