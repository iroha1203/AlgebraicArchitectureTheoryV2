# ArchSig v0.6.0 SHIGURE 図式補完・一段変更経路・合法状態移送 PRD

## 問い

既存の独立クレート `crates/shigure`（`archsig-shigure`）および `archsig.atom-definition/1`・`archsig.law/2`・`archsig.archmap/2`（`semantics "archsig/0.6.0"`）の SHIGURE 計算基盤の上で、**複数 PR の統合を表す固定図式の全補完（四角形・鎖・一般有限図式）、許容一段変更から生成する変更経路と細分化、および意味保存射に沿う合法状態の移送と共通操作語の保存（G-140 F・G）**を、一般の原始表示 IR と多項式／ideal 計算核から入口（入力層・CLI）から出力（復元・再評価検算・沈黙）まで一気通貫で成立させられるか。

本作業の一次仕様（target statement、受け入れ条件、失敗判定条件）はこの PRD に置く。
恒久的な I/O スキーマ、DSL 構文、標準構成規則、出力形式は実装と同期して `docs/tool/archsig_v0_6_0_io/` 配下の現行仕様書へ反映する。

---

## 現状診断と参照先

### 現状診断

- 現行の `tools/archsig_v0.6.0` は独立クレート `crates/shigure`（`archsig-shigure`）を持ち、`shigure presentation` / `comparison` / `change_spec` / `eval_condition` / `task` の 5 宣言と 3 種の問い（`shigure_preservation`・`shigure_solve`・`shigure_interaction`）によって、単一の意味保存変更の検査、条件付き解空間 $\mathcal{F}_{a,H,P}$ の計算と復元、座標面支持による相互作用解析を実行できる。
- 一方で、[全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376) の Phase 2（G-140 F・G）に相当する次の 3 領域が未実装である。
  1. **固定図式の全補完（G-140 F1 / [n1020 §16.7](../note/n1020_shigure_polynomial_specializations.md#diagram-completion)）**: 共通起点から分岐する複数 PR の統合（fork $b \xrightarrow{f} a \xleftarrow{g} c$ に対する可換四角形補完 $b \xleftarrow{u} z \xrightarrow{v} c$、$f \circ u = g \circ v$）や鎖・一般有限図式の補完を計算し、状態射と操作語翻訳の両方について可換性・内容保持・復元を検証する構成がない。
  2. **一段変更経路と細分化（G-140 F2–F3 / [n1020 §16.8](../note/n1020_shigure_polynomial_specializations.md#paths-and-state-transfer)）**: 許容一段変更の族 $\mathcal{E}_{1,H}$ から長さ $n$ の経路族 $\operatorname{Path}_{n,H}(a,b)$、経路の連結・合成、指定辺の $n$ 段細分化、および台帳移行の Boolean 4 順序（P5.1）と係数を状態に含む phase protocol の Idle 切替経路（P5.2）を計算する構成がない。
  3. **合法状態の移送と共通操作語の保存（G-140 G1–G3 / [ledger-specialization.md P5.3](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#p53--busy状態の移送は係数条件だけでは決まらない)）**: 意味保存射 $h_{01}: X_1 \to X_0$ と開始状態域 $\iota_0: D_0 \hookrightarrow X_0$ に対する合法 lift $m_{01}: D_0 \to X_1$（$h_{01} m_{01} = \iota_0$ かつ目標 phase Law 成立）、共通操作語定義域 $D_w$ 上の観測保存、2 段移送の fiber product 合成 $D_{02}$、および係数点が合法でも Busy 状態で失敗する移送の検出がない。
- **肥大化停止線の現在値**: 既存 `crates/computation/src/observed/` に加え、`crates/shigure` と `crates/input/src/law/shigure/` および `src/run/shigure.rs` の一部ファイルはすでに 800〜975 行に達している（`algebra/poly.rs` 975 行、`solver/restore.rs` 910 行、`solver/preservation.rs` 841 行、`ir/validate.rs` 811 行、`input/.../check_relations.rs` 898 行、`check.rs` 833 行、`parser.rs` 826 行、`src/run/shigure.rs` 916 行）。[Tool guideline](../tool/guideline.md#設計と実装) に従い、既存ファイルへ無条件に追記せず独立サブモジュールまたは責務分割で拡張する必要がある。

### 参照先

| 役割 | 参照先 |
| --- | --- |
| トラッキング・関連 Issue | [全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376)、[Phase 1 完了 Issue #6377](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6377) |
| ツール設計・品質規約 | [Tool guideline](../tool/guideline.md)、[Workflow guideline](../workflow/guideline.md)、[PRD guideline](guideline.md)、[語彙ルール](../workflow/vocabulary.md) |
| 現行 I/O・計算仕様 | [I/O 仕様](../tool/archsig_v0_6_0_io/README.md)、[Atom 定義](../tool/archsig_v0_6_0_io/definitions.md)、[ArchMap](../tool/archsig_v0_6_0_io/inputs.md)、[Law DSL](../tool/archsig_v0_6_0_io/law.md)、[核の構成](../tool/archsig_v0_6_0_io/computations.md)、[実行](../tool/archsig_v0_6_0_io/execution.md)、[型付き結果](../tool/archsig_v0_6_0_io/results.md)、[短い適合例](../tool/archsig_v0_6_0_io/validation.md) |
| SHIGURE 構想・多項式特殊化 | [n1019（とくに §§5.4–5.5）](../note/n1019_shigure_representability_design.md)、[n1020（とくに §§16.7–16.8・§17.4）](../note/n1020_shigure_polynomial_specializations.md)、[n1021](../note/n1021_unified_tool_suite_rising_sea.md) |
| SHIGURE 紙上証明（一次数学根拠） | [G-140 目標](../../research/goals/G-140-aat-semantic-change-category.md)、[G-140 紙上証明 README](../../research/designs/G-140-aat-semantic-change-category/README.md)、[G-140 図式・経路・状態移送](../../research/designs/G-140-aat-semantic-change-category/diagrams-paths-transfer.md)、[G-140 台帳特殊化（P5.1–P5.3・P6）](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md)、[G-141 有限計算（D1・D4・D5）](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md) |
| 既存ワークスペース | `tools/archsig_v0.6.0/Cargo.toml`、`crates/input/src/law/shigure/`、`crates/shigure/`、`src/run/shigure.rs`、`tests/fixtures/shigure-ledger/` |

---

## タスク固有の target statement（数学対応）

本 PRD が `crates/shigure` で有限特殊化として実装し、コード上の適用条件検査とテストで対応を検証する数学的構成は、以下の紙上証明条項に限定する。

| 対象機能 | 対応する紙上証明の条項 | 適用条件（コード上で明示検査） | 条件外時の振る舞い |
| --- | --- | --- | --- |
| 固定図式の全補完（四角形・鎖・一般有限図式） | [G-140 F1・F1.1–F1.2](../../research/designs/G-140-aat-semantic-change-category/diagrams-paths-transfer.md#定理-f1--独立な図式補完と2-fiber)、[G-141 D1・D4・D5](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md) | 有限対象・有限生成射・有限関係で表示される図式形 $J$ と部分図式 $K \hookrightarrow J$、全頂点・辺の有限多項式表示と有効な有限還元、商環上の ideal 所属判定の適用域内、未観測値の不在 | 無限図式・次数上界のない witness 系・商環所属適用外・非線形 $\mathbb{Q}/\mathbb{Z}$ 点存在判定・未観測依存は `undetermined`（暗黙に ambient 零へ強めない。また観測一致だけで図式可換性を代用しない） |
| 一段変更から生成する経路と細分化 | [G-140 F2–F3・F3.1](../../research/designs/G-140-aat-semantic-change-category/diagrams-paths-transfer.md#定理-f2--一段変更から生成する経路)、[P5.1–P5.2](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#p51--四つのflag順序) | 有限な一段許容変更規則 $\mathcal{E}_{1,H}$、明示された経路長 $n \ge 0$（$n=0$ は恒等変更）、統一された射の向き、各中間段の保存・評価条件と細分化合成一致の有限還元 | 係数曲線上の点列から実射・翻訳のない経路を生成しない（F3.1 で空を返す）。経路長未指定の無界探索・有限還元不能・係数域適用外は `undetermined` |
| 合法状態の移送と共通操作語の保存 | [G-140 G1–G2](../../research/designs/G-140-aat-semantic-change-category/diagrams-paths-transfer.md#定理-g1--合法状態の移送fiber)、[P5.3](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#p53--busy状態の移送は係数条件だけでは決まらない) | 意味保存射 $h_{01}: X_1 \to X_0$（語翻訳 $\tau$・観測 $o_1 = o_0 h_{01}$ 付き）、合法な開始状態域 $\iota_0: D_0 \hookrightarrow X_0$、有限多項式表示の移送規則 $m_{01}: D_0 \to X_1$、phase・操作 domain の有限表示 | 観測一致 $o_1 m_{01} = o_0 \iota_0$ だけで $h_{01} m_{01} = \iota_0$ を代用しない。旧語の lift 存在を $h_{01}$ の意味保存性から自動帰結させない。商環所属適用外・非線形点存在判定・未観測依存は `undetermined` |
| 移送の合成と fiber product | [G-140 G3](../../research/designs/G-140-aat-semantic-change-category/diagrams-paths-transfer.md#定理-g3--移送の合成) | 合成可能な移送列（$h_{01}, \iota_0, m_{01}$ と $h_{12}, \iota_1, m_{12}$ 等）、$D_{02} = D_0 \times_{m_{01}, X_1, \iota_1} D_1$ と合成語翻訳 $\tau_{01} \circ \tau_{12}$ の有限還元 | $m_{01}$ が $D_1$ を経由しない場合に $D_{02} \cong D_0$ と誤認せず、引き戻した部分域（空を含む）をそのまま返す。有限還元不能・未観測依存は `undetermined` |

---

## 要求

### R1. `crates/shigure` の直交モジュール拡張と中心 IR の先行固定

1. 既存の `crates/computation/src/observed/` へは新しい機能・分岐を追記せず、依存の向き `archsig-common` / `archsig-input` → `archsig-shigure` → `archsig`（CLI）を維持する。
2. [Tool guideline](../tool/guideline.md#設計と実装) の肥大化停止線に従い、目安 1,000 行に近づいている既存ファイル（`crates/shigure/src/algebra/poly.rs`・`solver/restore.rs`・`solver/preservation.rs`・`ir/validate.rs`、`crates/input/src/law/shigure/{parser,check,check_relations}.rs`、`src/run/shigure.rs`）へ新機能を無条件に追記しない。新規の図式・経路・移送機能は独立サブモジュール（例: `ir/diagram.rs`・`ir/path.rs`・`ir/transfer.rs`、`solver/diagram.rs`・`solver/path.rs`・`solver/transfer.rs`、入力層および CLI 側の対応サブモジュール）として配置し、必要であれば既存ファイルを先に責務分割して単一ファイル 1,000 行未満を維持する。
3. 個別の計算機能に着手する前に、次の中心 IR・検証済み型（`Checked*`）・出力型を先に固定する。
   - **射の向きの型レベル統一**: [G-140 共通規約](../../research/designs/G-140-aat-semantic-change-category/README.md#共通規約と射の向き)に従い、状態比較射の向き（`after -> before`、合成 $h_{02} = h_{01} \circ h_{12}$）と時間順（`before -> after`、反対圏 $\mathcal{C}_R^{\mathrm{op}}$）を IR 上で明示的に区別・統一し、状態射・操作語翻訳の合成順を型で保証する。
   - **図式補完 IR (`DiagramSpec` / `CheckedDiagramTask`)**: 有限図式形 $J$（頂点・生成射・合成関係）、固定部分圏 $K \hookrightarrow J$ と固定部分図式 $d$、補完対象の頂点・辺に対する許容変換仕様 $H$、全体または辺ごとの評価条件 $P$、および由来参照。
   - **一段変更経路・細分化 IR (`PathSpec` / `CheckedPathTask`)**: 一段許容変更規則の族 $\mathcal{E}_{1,H}$（係数切替・partial phase operation・比較射規則を含む）、始点・終点 $(a, b)$、明示的な段数 $n \ge 0$ または細分化対象辺 $e: a \to b$、各中間段の保存・評価条件、および由来参照。
   - **合法状態移送 IR (`TransferSpec` / `CheckedTransferTask`)**: 意味保存射 $h_{01}$（および 2 段以上では合成可能な射列）、許可開始状態域 $\iota_0: D_0 \hookrightarrow X_0$（phase と追加状態 Law 条件）、移送候補規則 $m_{01}: D_0 \to X_1$、検査対象の新側許可語 $w$ または旧側要求語 $v$、評価条件 $P$、および由来参照。

### R2. 図式補完・変更経路・合法状態移送の計算核

既存の多項式・ideal 計算核（`algebra`）と意味保存・条件付き解空間・復元機構（`solver`）を再利用し、直交分解を保ったうえで次の 3 計算核を構成する。

1. **固定図式の全補完（G-140 F1・F1.1–F1.2）**:
   - 各補完頂点・各補完生成射の保存義務（状態 Law 保存・生成操作閉性・遷移可換性・観測保存）に加え、図式 $J$ の全生成関係について **状態射の合成一致** と **操作語翻訳の合成一致** の両方を原始式から生成する。
   - 四角形補完では固定された 2 枝 $b \xrightarrow{f} a \xleftarrow{g} c$ と共通固定部分を保持し、補完頂点 $z$ と 2 射 $u: z \to b$・$v: z \to c$ および $f \circ u = g \circ v$ の全解・空性 witness・復元図式（全頂点・全辺の操作式・$h$・$\tau$）と独立した数学モデル再評価検算を返す。
   - 鎖補完では両端および指定中間頂点を固定し、全中間表示と各辺の実射・語翻訳を復元する。
   - 各辺の商環上 ideal 所属は既存 `quotient` 機構により ambient 多項式零へ強めず扱い、導出 witness の選択差を補完解の重複として数えない。
2. **一段変更経路・連結・細分化（G-140 F2–F3・F3.1・P5.1–P5.2）**:
   - $n = 0$（恒等変更：marked 版では端点一致で 1 点・不一致で空）および $n \ge 1$ の $\operatorname{Path}_{n,H}(a,b)$ を計算し、各段の比較射・語翻訳・中間表示・全体の合成射を復元・再評価検算する。
   - 2 経路の連結（共通端点一致と結合則）および指定辺 $e: a \to b$ の $n$ 段細分化 fiber（各細分辺が一段許容規則に属し、合成が状態射・語翻訳ともに $e$ に一致する解空間）を計算する。
   - 規則 $H$ が合成で閉じない場合に、合成射を一段許容変更と誤認しない。
   - 係数空間の点列（曲線）だけから実射・語翻訳のない経路を生まず、一段規則を恒等のみとしたときの異なる 2 点間の経路は空（`refuted`）とする（F3.1）。
   - 台帳の $X = V(\mu\delta(1-\rho))$ に対し、(a) Boolean 係数 $(0,0,0) \to (1,1,1)$ の全 6 順序から合法な 4 順序（`ρ,δ,μ` / `ρ,μ,δ` / `δ,ρ,μ` / `μ,ρ,δ`）を導出し残り 2 順序を 2 段目 $(1,1,0)$ の残差 1 で拒否すること（P5.1）、(b) 係数を状態成分に含む 1 つの phase protocol（Idle でのみ切替後 $f=0$ を domain とする partial flag operation）で全許可有限語の保存と 4 順序の実行経路を構成すること（P5.2）を一般構成から導出し、「拡大 protocol 内の実行経路」と「固定 protocol 間の変更経路」を出力上で区別する。
3. **合法状態の移送・共通操作語保存・移送合成（G-140 G1–G3・P5.3）**:
   - 移送候補 $m_{01}: D_0 \to X_1$ に対し、目標 phase の状態 Law 成立と厳密な lift 条件 $h_{01} \circ m_{01} = \iota_0$（観測一致 $o_1 \circ m_{01} = o_0 \circ \iota_0$ で代用しない）を原始式から生成し、解空間・空性 witness・復元移送式 $m_{01}$ と再評価検算を返す（G1）。
   - 新側の許可語 $w$ に対し、両側の phase・操作 domain から共通定義域 $D_w = m_{01}^{-1}\operatorname{Dom}_1(w) \cap \iota_0^{-1}\operatorname{Dom}_0(\tau w) \subseteq D_0$ を構成し、$D_w$ 上での $h_{01}\,\operatorname{eval}_1(w)\,m_{01} = \operatorname{eval}_0(\tau w)\,\iota_0$ と $o_1\,\operatorname{eval}_1(w)\,m_{01} = o_0\,\operatorname{eval}_0(\tau w)\,\iota_0$ を検証する。旧側の指定語 $v$ を移送後にも実行する要求（$\tau w = v$ かつ開始域が $D_w$ を経由する新語 $w$ の lift）は独立の探索条件として計算する（G2）。
   - 2 段以上の移送に対し、引き戻し定義域 $D_{02} = D_0 \times_{m_{01}, X_1, \iota_1} D_1$ と合成移送 $m_{02} = m_{12} \circ \operatorname{pr}_2$ を構成し、$h_{01} h_{12} m_{02} = \iota_0 \operatorname{pr}_1$・合成語翻訳の観測保存・結合則、および $m_{01}$ が $D_1$ を経由する場合（$D_{02} \cong D_0$）と経由しない場合（部分域への縮退または空）を区別して返す（G3）。
   - 台帳の Busy 状態移送対照例（P5.3: $\mathbb{Q}$ 上で $(1,0,0)$・Idle $(0,0)$ から `begin; apply_1` で得た Busy $(0,1,0)$ をそのまま $(0,0,0) \to (0,1,0)$ へ移す要求）で、係数点がすべて $X$ 上にあっても最終段 Busy Law $g_\rho = -1 \neq 0$ により `refuted`（空性 witness 付き）と検出し、係数条件だけで通さないことを検証する。

### R3. 現行入力層（`archsig-input`）拡張・変換層・最小 CLI 入口・沈黙規律

1. 既存の入力版（`archsig.atom-definition/1`・`archsig.archmap/2`・`archsig.law/2`、`semantics "archsig/0.6.0"`）を維持し、予約語を増やさず文脈キーワード `shigure` の配下に図式補完・一段変更経路・合法状態移送の最小宣言を追加する。既存の通常テストおよび既存 SHIGURE テスト・フィクスチャを一切退行させない。
2. 結論注入の禁止（補完済み図式結果、計算済み経路列、移送可否、共通定義域の結論相当欄を Law 入力に含めた場合は構文・変換検査で拒否）および由来分離（`Origin.kind` の明示要求、未参照 `Origin` の非混入、欠測座標の零補完禁止）を型と検査で強制する。
3. `archsig check` / `archsig run` へ最小の 3 問いを追加する（既存の通常問いとの混在禁止・SHIGURE 問い同士の複数同時実行・`--out` への `archsig.result/4` 保存は現行 SHIGURE 経路の規約を踏襲する）。
   - `shigure_diagram(<Task>)`: 固定図式の補完（四角形・鎖・一般有限図式）
   - `shigure_path(<Task>)`: 許容一段変更経路の探索・連結・細分化
   - `shigure_transfer(<Task>)`: 合法状態の移送 lift・共通操作語保存・移送合成
4. 出力には既存の `ShigureOutcome` 規約と一貫して、係数域・点集合域の明示、由来・適用条件検査結果、復元された図式／経路／移送式と `scope: "mathematical_model_reevaluation"` の再評価検算結果、および適用条件外・未観測依存時の理由付き `verdict: "undetermined"`（CLI では `status: "partial"`・exit 2）を保持する。

### R4. 恒久仕様書の同期更新

1. 本 PRD で導入する DSL 宣言構文、標準構成・適用条件・沈黙理由、CLI の問い、型付き結果スキーマ、適合例を、同じ変更の中で `docs/tool/archsig_v0_6_0_io/` 配下の恒久仕様書（[law.md](../tool/archsig_v0_6_0_io/law.md)・[computations.md](../tool/archsig_v0_6_0_io/computations.md)・[execution.md](../tool/archsig_v0_6_0_io/execution.md)・[results.md](../tool/archsig_v0_6_0_io/results.md)・[validation.md](../tool/archsig_v0_6_0_io/validation.md)、必要に応じ [inputs.md](../tool/archsig_v0_6_0_io/inputs.md)）および [tools/archsig_v0.6.0/README.md](../../tools/archsig_v0.6.0/README.md) へ反映する。

---

## 受け入れ条件（Acceptance Criteria）

| ID | 区分 | 受け入れ条件 | 確認証拠 |
| --- | --- | --- | --- |
| **AC1** | モジュール境界と IR 先行固定 | `crates/computation/src/observed/` への変更が 0 件であり、`crates/shigure`・`crates/input/src/law/shigure/`・`src/run/` の図式補完・変更経路・状態移送の IR（`Checked*` 含む）・計算核・変換層・CLI 入口が独立サブモジュールとして責務分離され、新規および変更対象の Rust ファイルがいずれも目安 1,000 行未満に収まっている。射の向き（状態比較射と時間順）が型で統一されている。 | 変更ファイル一覧・行数計測、依存グラフ、IR 単体テスト |
| **AC2** | 入力層後方互換拡張と入力保護 | `archsig.law/2`（`semantics "archsig/0.6.0"`）の文脈キーワード `shigure` 配下に図式・経路・移送宣言を追加し、`archsig-input → archsig-shigure` 変換層で型・参照・循環・由来・係数域整合を検査できる。結論注入・意味 Law 編集・不正参照・未宣言辺は入力／変換検査（exit 65）で拒否され、既存の全テスト・既存フィクスチャ（通常経路および既存 SHIGURE 経路）が一切退行せず通過する。 | `cargo test --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml` 全通過、入力層・負例テスト |
| **AC3** | 図式補完の垂直スライス（G-140 F1・F1.1–F1.2） | 独立フィクスチャを用いた `archsig run`（`shigure_diagram`）で次をすべて得る。(a) 複数 PR 統合の四角形補完（fork $b \xrightarrow{f} a \xleftarrow{g} c$ から $z, u, v$ を補完し、状態射と語翻訳の両方で $f \circ u = g \circ v$・各辺保存・内容保持を満たす解を復元・再評価一致）。(b) 両立不能な四角形に対する `refuted` と検算済み空性 witness（$1 = \sum h_i f_i$）。(c) 鎖補完で中間表示・実射・語翻訳を復元。(d) 2 枝の観測一致や係数条件だけでは四角形補完を成立扱いしない対照例、および商環上 ideal 所属を ambient 零へ強めない検証。 | 実バイナリ E2E テストと出力 JSON（復元図式・可換残差・空性 witness・`reevaluation.matched = true`） |
| **AC4** | 一段変更経路・細分化と台帳 4 順序（G-140 F2–F3・F3.1・P5.1–P5.2） | 独立フィクスチャを用いた `archsig run`（`shigure_path`）および計算核テストで次をすべて得る。(a) 台帳 $V(\mu\delta(1-\rho))$ で $(\delta,\mu,\rho)$ を $(0,0,0) \to (1,1,1)$ へ切り替える全 6 順序から 4 順序（`ρ,δ,μ` / `ρ,μ,δ` / `δ,ρ,μ` / `μ,ρ,δ`）を合法経路として復元し、残り 2 順序（`δ,μ,ρ` / `μ,δ,ρ`）を 2 段目 $(1,1,0)$ の残差 1 で拒否する。(b) 係数を状態に含む 1 つの phase protocol で Idle 切替の 4 実行経路と全許可有限語保存を検証し、拡大 protocol 内実行経路と固定 protocol 間変更経路を区別する。(c) $n=0$ 恒等経路・経路連結（結合則）・指定辺の $n$ 段細分化 fiber の成立と不成立。(d) F3.1 対照例（恒等一段規則の $\mathbb{A}^1$ で異なる 2 点間の経路が空で `refuted`）。 | 実バイナリ E2E テスト、単体・パラメトリックテスト、出力 JSON |
| **AC5** | 合法状態移送・共通操作語保存・合成（G-140 G1–G3・P5.3） | 独立フィクスチャを用いた `archsig run`（`shigure_transfer`）および計算核テストで次をすべて得る。(a) 意味保存射 $h_{01}$ と開始域 $\iota_0: D_0 \hookrightarrow X_0$ に対する $h_{01} m_{01} = \iota_0$＋目標 phase Law の lift 解復元と再評価一致、および観測一致だけで $h_{01} m_{01} \neq \iota_0$ の候補を拒否する対照例。(b) 共通定義域 $D_w$ 上での新語 $w$ の観測保存検算と、旧語 $v$ の lift 存在の独立判定（成立例・不成立例）。(c) 2 段移送の fiber product 定義域 $D_{02}$ と合成移送 $m_{02}$ の構成（$m_{01}$ が $D_1$ を経由し $D_{02} \cong D_0$ となる例と、経由せず部分域へ縮退／空となる例、および 3 段の結合則）。(d) P5.3 対照例（台帳の係数点 $(1,0,0) \to (0,0,0) \to (0,1,0)$ はすべて $X$ 上でも、Busy 状態 $(0,1,0)$ の移送は最終段 Busy Law $g_\rho = -1$ で `refuted`）。 | 実バイナリ E2E テスト、単体・パラメトリックテスト、出力 JSON |
| **AC6** | 沈黙規律と代数的性質の網羅検証 | 状態射・語翻訳合成の結合則、係数域・点集合域の区別（代数閉包 vs $\mathbb{Q}/\mathbb{Z}/\mathbb{F}_p$）、および適用条件外（未観測座標依存、非線形 $\mathbb{Q}/\mathbb{Z}$ 点存在判定、商環所属適用外、無界探索／有限還元不能な入力）で誤った `established` / `refuted` を返さず理由付き `undetermined`（CLI は `partial` / exit 2）を返すことを単体・パラメトリック・E2E テストで確認する。 | 代数的性質テスト、沈黙・負例 E2E テスト |
| **AC7** | 仕様書同期と品質確認 | 導入した DSL 宣言・標準構成・CLI 問い・出力スキーマ・適合例が `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` に同期反映されている。`rustfmt`・関連 Clippy lint・`git diff --check`・不可視／双方向制御 Unicode 検査・語彙ルール検査を通過する。 | 更新された仕様書差分、検証コマンド出力 |
| **AC8** | 代表規模ベンチマーク実測 | 数百対象・数千 Atom 級の固定代表入力（既存ベンチ入力および図式・経路・移送を含む固定入力）について、変更前後の実行時間と最大 RSS を実測比較し、既存経路の著しい退行がなく、新規 SHIGURE 経路の計算費用が実測値として Issue / PR に記録されている。 | Issue / PR に記録した実行時間・最大 RSS の実測比較ログ |

---

## この作業での失敗判定条件（Failure Contract）

次のいずれかに該当する場合、本 PRD は未達（失敗）と判定する。

1. **肥大化停止線・境界違反**: `crates/computation/src/observed/` へ追記した場合、または目安 1,000 行を超える既存ファイルへ責務分割なしに図式・経路・移送の実装を継ぎ足した場合。
2. **題材固有ハードコード**: 台帳の 4 順序（P5.1）・Idle 切替 protocol（P5.2）・Busy 移送失敗（P5.3）や特定の四角形例を、一般の図式・経路・移送 IR と多項式／ideal 計算核から導出せず、専用分岐やパターンマッチで出力した場合。
3. **数学的条件のすり替え・弱化**:
   - 2 枝の観測一致や係数条件（例: $\mu\delta = 0$）だけで四角形補完の全射・可換性を成立扱いした場合。
   - 係数空間の点列（曲線）だけから実射・語翻訳のない変更経路を生成した場合（F3.1 違反）。
   - 拡大 protocol 内の実行経路と、各係数で別個に取った固定 protocol 間の変更経路を混同した場合（P5.2 違反）。
   - 観測一致 $o_1 m_{01} = o_0 \iota_0$ だけで厳密な lift 条件 $h_{01} m_{01} = \iota_0$ や目標 phase Law を代用した場合（G1・P5.3 違反）。
   - 旧語の lift 存在を $h_{01}$ の意味保存性から自動帰結させた場合、または 2 段移送の $D_{02}$ 引き戻しを行わず常に $D_0$ 全域で合成可能と扱った場合（G2・G3 違反）。
   - 商環上の ideal 所属を ambient 多項式零へ黙って強めた場合。
4. **適用条件の無検査・沈黙違反・係数域混同**: 係数域・点集合域や有限還元条件を検査せず、条件外入力に対して誤った `established` / `refuted` や暗黙の近似を返した場合。
5. **結論注入・由来混同・復元なき真偽出力**: 補完済み図式・計算済み経路・移送結果などの結論相当欄を入力で受理した場合、由来（`Origin.kind`）を喪失した場合、または真偽フラグだけを返し具体的な図式・経路・移送式への復元と元式への独立再評価検算を欠く場合。
6. **仕様書・テスト・ベンチの不足または退行**: AC1〜AC8 のいずれかの一次証拠が欠けている場合、または既存 `archsig_v0.6.0` の通常経路・SHIGURE 経路テストが退行した場合。

---

## 実装計画（垂直スライス順）

1. **Step 1 — 図式・経路・移送の IR とモジュール境界の固定**:
   `crates/shigure/src/ir/` に `diagram`・`path`・`transfer` の独立サブモジュール（射の向き型・`Checked*` 検証済み構築経路・結果型拡張を含む）を定義する。既存ファイルが 1,000 行に近づく箇所は先に責務分割する。
2. **Step 2 — 計算核（図式補完・変更経路・合法状態移送）の実装と代数的検証**:
   `crates/shigure/src/solver/` に独立サブモジュール（`diagram`・`path`・`transfer`）を実装し、既存の `algebra`・`preservation`・`restore` を再利用して F1–F3・G1–G3 の保存方程式生成・商環所属・解空間計算・空性 witness・復元・再評価検算を実装する。クレート内の単体・パラメトリックテストで四角形・鎖・F3.1・P5.1–P5.3・G1–G3・沈黙を通す。
3. **Step 3 — 入力層（`archsig-input`）後方互換拡張と変換層**:
   `crates/input/src/law/shigure/` に図式・経路・移送宣言のパーサと静的検査を独立サブモジュールとして追加し、`crates/shigure/src/convert/` の独立変換モジュールから `CheckedDiagramTask` / `CheckedPathTask` / `CheckedTransferTask` を構築する。結論注入・不正参照・由来欠落の拒否と既存全テスト非退行を確認する。
4. **Step 4 — CLI 入口・E2E フィクスチャ検証**:
   `src/run/` の SHIGURE 実行経路を責務分割したうえで `shigure_diagram`・`shigure_path`・`shigure_transfer` を接続し、`archsig check` / `archsig run`（`--out` 保存含む）の実バイナリ E2E テストで AC3〜AC6 を検証する。
5. **Step 5 — 恒久仕様書同期・品質検査・代表規模ベンチ実測**:
   `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` を同期更新し、`rustfmt`・Clippy・`git diff --check`・Unicode／語彙検査・代表規模ベンチマーク（実行時間・最大 RSS の前後比較）を実施して記録する。

---

## 対象外（Non-Goals）

以下は本 PRD の対象外とし、本作業では実装・先回り設計を行わない。

- **複数解釈族の頑健判定と包含極小の追加観測**（Phase 3 予定: G-140 E3–E5・G-141 D6–D7・G-142 G — 実現族 $U_b$ の 3 量化、Chevalley 四分類、包含極小の分離観測列挙）
- **高次変形・syzygy 障害・Artin 試験・診断層と Atlas 比較**（Phase 4 予定: G-141 E/F/G・G-142 A–F — 全 syzygy 平方零 lift 複体、初回次数 $\nu$ の Artin 試験、局所 adapter の cycle 障害と SAGA / K0–K1 診断比較、値合流の Mayer–Vietoris）
- **同梱 SKILL（`tools/archsig_v0.6.0/skills/`）の SHIGURE 対応**および代表 OSS での SKILL 通し実測 QA（Phase 5 予定）
- **運用最適化の先回り実装**: キャッシュ（`--reuse` の SHIGURE 再利用対応）、計算予算制御、配布パッケージング、細かな終了コード・エラー形式の作り込み（[Tool guideline](../tool/guideline.md#作り方) に従い、同梱 SKILL 通し実測後に検討）
- **一般階数（sort rank > 1）の複数 chart 貼り合わせ・商 stack** および **SHIGURE 問いと通常 observed 問いの同一 `run` 混在実行**
- **外部手法との接続**: TLA+ モデル生成・読戻し（[n1020 §17.6](../note/n1020_shigure_polynomial_specializations.md#176-tlaへの対応)）、静的解析器からの自動取込み、ArchView / FieldSig 側の改修
- **Lean 形式化（`Formal/`）・数学本文（保護対象）・Website の変更**
- **CI への新規 job / step の恒久追加**

---

## 停止条件

次のいずれかに該当した場合、場当たり的に実装や仕様を埋めず、判断事項と根拠を整理して停止し人間へ戻す。

1. **既存入力仕様・既存 SHIGURE 宣言との意味衝突**: `archsig.law/2` / `archsig.archmap/2`（`semantics "archsig/0.6.0"`）の既存構文・既存 SHIGURE 5 宣言（`presentation` / `comparison` / `change_spec` / `eval_condition` / `task`）と両立しない設計変更が必要と判明した場合。
2. **紙上証明との不整合または未定義境界**: G-140 F・G または G-141 D1–D5 の仮定・有限還元条件・射の向き・2-fiber 同型比較の扱いに、仕様書未定義の設計判断が必要な境界が見つかった場合。
3. **計算量の現実的破綻**: 四角形補完・複数段経路・2 段移送の連立多項式系に対して、$\mathbb{Q}$ 上の Gröbner 基底計算や商環層別が現実的な時間・メモリで収束せず、アルゴリズム選定や対象範囲の切り直しが必要になった場合。
4. **CI 時間制約への抵触**: ワークスペース全体のビルド・テストが [Tool guideline](../tool/guideline.md#ci-への追加) の想定 CI 3 分上限を超える兆候が出た場合。
