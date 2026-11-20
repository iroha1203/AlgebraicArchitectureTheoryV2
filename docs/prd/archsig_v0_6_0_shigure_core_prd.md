# ArchSig v0.6.0 SHIGURE 基盤 IR・多項式条件付き解空間・意味保存変更 PRD

## 問い

既存の Atom 定義・Law DSL・ArchMap（`archsig.atom-definition/1`・`archsig.law/2`・`archsig.archmap/2`、`semantics "archsig/0.6.0"`）を出発点として、SHIGURE の原始表示・意味保存変更・条件付き解空間 $\mathcal{F}_{a,H,P}$ を独立クレート `crates/shigure` 上に構成し、**守る意味 Law と変更可能な表示 Law および目的の評価条件（等式 $V(f)$・可逆条件 $D(g)$）を分離した非線形多項式制約の計算と、具体的な操作式・状態比較・語翻訳への復元**を、入口（入力層・CLI）から出力まで一気通貫で成立させられるか。

本作業の一次仕様（target statement、受け入れ条件、失敗判定条件）はこの PRD に置く。
恒久的な I/O スキーマ、DSL 構文、標準構成規則、出力形式は実装と同期して `docs/tool/archsig_v0_6_0_io/` 配下の現行仕様書へ反映する。

---

## 現状診断と参照先

### 現状診断

- 現行の `tools/archsig_v0.6.0` は Atom 定義・Law DSL・ArchMap の三入力から、有限候補域・整数アフィン fiber・局所化・部品表現（`prepare`/`scopes`）・局所組立て（`assemble`/`assemble_map`）を計算できる。
- 一方で、次の構造と計算が不足している。
  1. **非線形多項式制約と評価条件 $P \hookrightarrow T$ の計算**: 現行の `solve`/`repair` は有限列挙と整数アフィン（`Lx=c`）に留まり、台帳移行例（[n1020 §16.4](../note/n1020_shigure_polynomial_specializations.md#164-二変更の相互作用と更新の消失)）のような非線形残差 $\mu\delta(1-\rho)=0$ と可逆評価条件 $D(\mu\delta)$ から $\rho=1$ を導出し操作式へ復元する計算を持たない。
  2. **守る意味 Law と編集可能な表示 Law の分離**: phase 状態・操作語翻訳 $\tau$・状態比較 $h$・許容変換仕様 $H$（固定部分と編集可能部分の区別）を統一的に表現する中間表現（IR）が存在しない。
  3. **相互作用の参加変数数と極小不成立部分族**: 複数変更 parameter の残差 ideal に対し、座標面支持から相互作用に参加する変更数 $r$ と極小不成立部分族を求める計算を持たない。
  4. **コードベースの肥大化**: `tools/archsig_v0.6.0/crates/computation/src/observed/` 配下は 200 ファイル超・約 29 万行（`environment.rs` 12,626 行、`evaluate.rs` 12,491 行、`result.rs` 6,589 行）に達しており、ここへ直接追記することは [Tool guideline](../tool/guideline.md#設計と実装) の肥大化停止線に反する。

### 参照先

| 役割 | 参照先 |
| --- | --- |
| トラッキング・対象 Issue | [全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376)、[本 PRD 実装 Issue #6377](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6377) |
| ツール設計・品質規約 | [Tool guideline](../tool/guideline.md)、[Workflow guideline](../workflow/guideline.md)、[語彙ルール](../workflow/vocabulary.md) |
| 現行 I/O・計算仕様 | [I/O 仕様](../tool/archsig_v0_6_0_io/README.md)、[Atom 定義](../tool/archsig_v0_6_0_io/definitions.md)、[ArchMap](../tool/archsig_v0_6_0_io/inputs.md)、[Law DSL](../tool/archsig_v0_6_0_io/law.md)、[核の構成](../tool/archsig_v0_6_0_io/computations.md)、[実行](../tool/archsig_v0_6_0_io/execution.md)、[型付き結果](../tool/archsig_v0_6_0_io/results.md) |
| SHIGURE 構想・多項式特殊化 | [n1019](../note/n1019_shigure_representability_design.md)、[n1020（とくに §16・§17）](../note/n1020_shigure_polynomial_specializations.md)、[n1021](../note/n1021_unified_tool_suite_rising_sea.md)、[n1018](../note/n1018_archsig_practical_validation_retrospective.md) |
| SHIGURE 紙上証明（一次数学根拠） | [G-139 紙上証明](../../research/designs/G-139-aat-law-generated-relative-geometry/README.md)、[G-140 条件付き変更](../../research/designs/G-140-aat-semantic-change-category/conditional-changes.md)、[G-140 台帳特殊化](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md)、[G-141 有限計算](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md)、[G-141 相互作用](../../research/designs/G-141-aat-coherent-repair-effectivity/interaction-families.md) |
| 既存ワークスペース | `tools/archsig_v0.6.0/Cargo.toml`、`crates/common`、`crates/input`、`crates/computation`、`src/` |

---

## タスク固有の target statement（数学対応）

本 PRD が `crates/shigure` で有限特殊化として実装し、コード上の適用条件検査とテストで対応を検証する数学的構成は、以下の紙上証明条項に限定する。

| 対象機能 | 対応する紙上証明の条項 | 適用条件（コード上で明示検査） | 条件外時の振る舞い |
| --- | --- | --- | --- |
| 原始表示と型付き affine / 多項式 term の評価一致 | G-139 P0–P1、[G-140 P0.1](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#定理-p01--型付きaffine-termの評価一致) | 有限 sort・有限 phase・有限操作・有限 Law、型付き構文木と係数環の整合、未観測値の不在 | 型・参照不正は入力エラー、未観測値依存は不足位置を返して `undetermined` |
| 意味保存射・操作語翻訳による全許可有限語の保存 | G-140 A2・[P1](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#定理-p1--原子操作の全語と係数空間)・[P3–P5](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#定理-p3--snapshotの合法family-vμδ) | 生成操作ごとの状態 Law 閉性（商環上の ideal 所属を含む）と観測保存方程式の有限還元 | 有限還元不能または商環所属判定の適用域外は `undetermined`（暗黙に ambient 零へ強めない） |
| 条件付き解空間 $\mathcal{F}_{a,H,P}$ と復元 | [G-140 E1–E2](../../research/designs/G-140-aat-semantic-change-category/conditional-changes.md#定理-e2--評価条件のfiber)・[P6](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#p6--eの評価fiberへの同定)、[G-141 D1・D4・D5](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md) | 有限個の候補変数・等式 $V(f)$・可逆条件 $D(g)$（$ug-1=0$）。係数域ごとの有効算法（$\mathbb{Q}$ 多項式 ideal と代数閉包空性 $1\in I$、$\mathbb{Z}/\mathbb{Q}$ アフィン、$\mathbb{F}_p$ 有限全列挙） | $\mathbb{Q}$/$\mathbb{Z}$ 非線形方程式の有理点・整数点存在判定など一般解法の適用外、または D8 型無限表示は `undetermined` と理由を返す |
| 相互作用の参加変数数 $r$ と極小不成立部分族 | [G-141 F10–F12](../../research/designs/G-141-aat-coherent-repair-effectivity/interaction-families.md#定理-f11--全可換環上の座標面ideal) | 閉条件で表される自由 parameter chart $k[t_1,\ldots,t_n]$、有効な係数零判定、有限個の残差多項式への有効有限還元 | 開条件が本質的に絡む変更や有限還元不能な残差は閉条件へ丸めず `undetermined` |

---

## 要求

### R1. 独立クレート `crates/shigure` と中心 IR の先行固定

1. `tools/archsig_v0.6.0/Cargo.toml` のワークスペースメンバーに新規クレート `crates/shigure`（パッケージ名 `archsig-shigure`）を追加する。
2. 依存の向きを `archsig-common` / `archsig-input` → `archsig-shigure` → `archsig`（CLI）に保ち、既存の `crates/computation/src/observed/` へは新しい機能や分岐を追記しない。
3. 既存の有限候補・整数アフィン計算（`archsig-computation` 側の純粋計算部品）を再利用する場合は、明示的な変換層を通じて接続する。
4. `crates/shigure` 内の各ソースファイルは責務ごとに小さく分割し、単一ファイル 1,000 行未満を目安に保つ。
5. 個別の計算機能に着手する前に、次の中心データ構造（IR）とモジュール境界を先に固定する。
   - **原始表示 IR (`Presentation`)**: sort、phase、状態座標、型付き affine / 多項式 term、観測写像、守る意味 Law（`semantic` / `required`）と編集可能な表示 Law（`representation`）の区別、状態比較 $h$、操作語翻訳 $\tau$、および元の Atom 定義・Law・ArchMap 位置への由来参照。
   - **許容変換仕様・評価条件 IR (`ChangeSpec` / `EvalCondition`)**: 固定する部分表示、変更可能な宣言・表示 Law、探索変数と係数域（$\mathbb{Z}$・$\mathbb{Q}$・$\mathbb{F}_p$）、等式条件 $V(f)$ と可逆条件 $D(g)$。
   - **多項式・ideal 計算核 (`algebra`)**: 単項式・多変数多項式（$\mathbb{Z}$・$\mathbb{Q}$・$\mathbb{F}_p$）、単項式順序、$\mathbb{Q}$ 上の Gröbner 基底、ideal 所属判定と所属 witness（$f = \sum h_i f_i$）、Rabinowitsch 補助式 $ug-1=0$ による可逆条件処理と代数閉包空性判定（$1 \in I$）、$\mathbb{Z}/\mathbb{Q}$ アフィン系および $\mathbb{F}_p$ 有限全列挙。
   - **意味保存・解空間・相互作用エンジン (`solver`)**: 原始表示から保存残差方程式・状態 Law 閉性（商環上の ideal 所属）を生成し、$\mathcal{F}_{a,H,P}$ の計算、解・空性 witness の生成、具体的な操作式・状態比較 $h$・語翻訳 $\tau$ への復元、および座標面支持による相互作用の参加変数数 $r$・極小不成立部分族を算出する。

### R2. 現行入力層（`archsig-input`）の拡張と変換層

1. 既存の入力版（`archsig.atom-definition/1`・`archsig.archmap/2`・`archsig.law/2`、`semantics "archsig/0.6.0"`）を維持したまま、既存入力の構文・意味・回帰テストを一切壊さずに SHIGURE 用の最小宣言を拡張する。
2. 拡張する表現要素は、次の 5 点に絞る（将来の PRD で追加する図式・経路・複数解釈族は今回の構文へ先回り追加しない）。
   - **由来種別の明示**: `Origin` で静的解析・実行観測・LLM 読解候補・人間採用の区別を保持できること（既存 `Origin` との後方互換を保つ）。
   - **phase・操作・状態 Law・観測写像**: phase 付き状態座標、生成操作（遷移式）、守る意味 Law と編集可能な表示 Law の区別、観測写像。
   - **状態比較と操作語翻訳**: 変更前後を結ぶ状態比較 $h$、操作語翻訳 $\tau$（空語への翻訳を含む）。
   - **許容変換仕様 $H$**: 固定する宣言・Law、編集を許す操作式・表示 Law、探索変数と係数域。
   - **評価写像 $v$ と評価条件 $P$**: 評価式と等式条件（$f = 0$）・可逆条件（$D(g)$）。
3. `archsig-input → archsig-shigure` の変換層を独立モジュールとして置き、構文・型・参照・評価一致・適用条件を検査する。既存の結論注入禁止（残差 ideal や解・空性・参加変数数を外部入力として受け取らない）を型と検証で強制する。

### R3. 最小 CLI 入口・型付き出力・沈黙の規律

1. 既存の `archsig check` / `archsig run` から SHIGURE 計算を実行できる最小の問いを追加する。
   - 意味保存変更の検査（生成操作の保存・商環での状態 Law 閉性・全許可有限語の保存根拠）
   - 条件付き解空間 $\mathcal{F}_{a,H,P}$ の計算と復元（解空間の残差 ideal、空性証明 $1 = \sum h_i f_i$ または具体的解・自由 parameter、元の操作式・状態表示・$h$・$\tau$ への復元）
   - 相互作用の解析（座標面支持による参加変数数 $r$ と極小不成立部分族）
2. 出力には次を必ず保持する。
   - 係数域の明示（代数閉包上の幾何点判定と $\mathbb{Q}$ 点・$\mathbb{Z}$ 点・$\mathbb{F}_p$ 点の区別を混同しない）
   - 入力の由来（`Origin`）・参照位置・適用条件の検査結果
   - 復元した操作式・状態表示・$h$・$\tau$ の再評価一致の確認結果
3. **判断不能（沈黙）の厳守**:
   - 適用条件を外れる入力（例：$\mathbb{Q}$ 上で代数閉包非空だが有理点・整数点存在の判定を求められた非線形系、未観測値への依存、有限還元できない無限表示、非対応の係数環・演算）は、誤った判定や暗黙の近似を返さず、理由・欠測位置・適用外条件を明示した `undetermined`（判断不能／未対応）を正常出力として返す。
   - 出力の数学的計算結果と、実コードへの復元・変更後再観測の確認は区別して扱う。

### R4. 仕様書の同期更新

1. 本 PRD で導入する入力構文、標準構成、CLI の問い、型付き結果スキーマは、同じ変更の中で `docs/tool/archsig_v0_6_0_io/` 配下の恒久仕様書（[inputs.md](../tool/archsig_v0_6_0_io/inputs.md)・[law.md](../tool/archsig_v0_6_0_io/law.md)・[computations.md](../tool/archsig_v0_6_0_io/computations.md)・[execution.md](../tool/archsig_v0_6_0_io/execution.md)・[results.md](../tool/archsig_v0_6_0_io/results.md)・[validation.md](../tool/archsig_v0_6_0_io/validation.md)）および `tools/archsig_v0.6.0/README.md` へ反映する。

---

## 受け入れ条件（Acceptance Criteria）

| ID | 区分 | 受け入れ条件 | 確認証拠 |
| --- | --- | --- | --- |
| **AC1** | 独立クレートと IR 境界 | `tools/archsig_v0.6.0/crates/shigure` がワークスペースメンバーとして独立構成され、`crates/computation/src/observed/` へ新機能・分岐を直接追記せずに、原始表示 IR・許容変換仕様 $H$・評価条件 $P$・多項式計算核が型安全に実装されている。`crates/shigure` 内の各ファイルは目安 1,000 行未満で責務分離されている。 | `Cargo.toml`、`crates/shigure/` のモジュール構成・行数、依存グラフ、単体テスト |
| **AC2** | 入力層拡張と後方互換 | `archsig.atom-definition/1`・`archsig.archmap/2`・`archsig.law/2`（`semantics "archsig/0.6.0"`）を拡張し、phase・操作・守る意味 Law / 編集可能な表示 Law・状態比較 $h$・語翻訳 $\tau$・許容変換 $H$・評価条件 $P$・由来種別を記述・検査し、`shigure` IR へ変換できる。既存の `archsig_v0.6.0` 全テスト・既存フィクスチャが一切退行せず通過する。結論注入や不正参照・型不一致は入力検査で拒否される。 | `cargo test --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml` 全通過、入力層単体・負例テスト |
| **AC3** | 台帳移行の通し垂直スライス（G-140 P0–P6） | [ledger-specialization.md](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md) の単一台帳 → base+delta 台帳移行を独立フィクスチャとして `archsig run` で実行し、次をすべて得る。(a) 原子操作の保存方程式 $ac+bd=1, ar+bs=0$ および $p=(1,1)$ の marked fiber 復元。(b) snapshot 方式の非線形保存族 $V(\mu\delta)$ と、評価条件 $D(\mu)$（$\delta=0$ 強制）・$D(\delta)$（$\mu=0$ 強制）・$D(\mu\delta)$（空性証明 $1 \in I$）。(c) 許容変換 $H$ を $\mathrm{finish}_\rho$ と Busy 表示 Law 編集可へ広げた $V(\mu\delta(1-\rho)) \cap D(\mu\delta)$ から $\rho=1$ を導出し `finish_snap` と全状態 Busy を復元・再評価一致。(d) 旧 Busy Law 固定の対照条件では依然空であること。 | 実バイナリ E2E テストと出力 JSON（残差 ideal、空性 witness $1=\sum h_i f_i$、復元操作式・$h$・$\tau$） |
| **AC4** | 相互作用の参加変数数（G-141 F10–F12） | 閉条件の自由 parameter chart に対し、残差 ideal の座標面支持から相互作用に参加する変更数 $r$ と極小不成立部分族を正確に計算する。台帳の $\mu\delta$（2 変数相互作用、極小不成立部分族 $\{\delta,\mu\}$）、単変数高次 $t^m$（1 変数相互作用）、および 3 変数例 $\mu\delta(1-\rho)$ における $\rho=0$ 面の不成立と $\rho=1$ 追加による解消を区別して返す。 | 単体・パラメトリックテストおよび CLI 実行結果 |
| **AC5** | 多項式・ideal 計算核の代数的性質と沈黙の規律 | (a) $\mathbb{Q}$ 上の Gröbner 基底・ideal 所属判定・証明 witness（$f=\sum h_i f_i$ の検算一致）・Rabinowitsch 可逆条件・商環での ideal 所属判定（ambient 零へ強めないこと、例：$R[y]/(ay)$ で $y=0$ の条件）および $\mathbb{Z}/\mathbb{Q}$ アフィン・$\mathbb{F}_p$ 全列挙の正しさを単体・パラメトリックテストで検証する。(b) $x^2+1=0$ のような代数閉包非空・$\mathbb{Q}$ 点不存在の区別、未観測欠測、適用条件外の入力に対して誤判定・暗黙近似をせず理由付きの `undetermined`（沈黙）を返す。 | 代数的性質の単体・property テスト、沈黙・負例テスト |
| **AC6** | 仕様書同期と品質確認 | 導入した入力構文・標準構成・問い・出力スキーマが `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` に同期反映されている。`rustfmt`・関連 Clippy lint・`git diff --check`・不可視/双方向制御 Unicode 検査・語彙ルール検査を通過する。 | 更新された仕様書差分、検証コマンド出力 |
| **AC7** | 代表規模ベンチマーク実測 | 数百対象・数千 Atom 級の固定代表入力（および既存ベンチ入力）に対して、本変更前後の実行時間と最大 RSS を実測比較し、既存経路の著しい退行がなく、SHIGURE 経路の計算費用が実測値として記録されている。 | Issue / PR に記録した実行時間・最大 RSS の実測比較ログ |

---

## この作業での失敗判定条件（Failure Contract）

次のいずれかに該当する場合、本 PRD は未達（失敗）と判定する。

1. **既存モジュールへの増築**: `crates/computation/src/observed/` の既存肥大化ファイルへ SHIGURE の計算核や分岐を直接追記した場合。
2. **表現・IR の後回しや特例ハードコード**: 台帳例（$\mu\delta$ や $\rho=1$）に特化した専用コード・パターンマッチで答えを出しており、一般的な原始表示 IR と多項式 ideal 計算核からの導出になっていない場合。
3. **適用条件の無検査・沈黙違反**: 係数域（代数閉包 vs $\mathbb{Q}$/$\mathbb{Z}$/$\mathbb{F}_p$）や有限還元条件を検査せず、条件外入力に対して誤った `established` / `refuted` や暗黙近似を返した場合、または商環上の ideal 所属を ambient 多項式零へ黙ってすり替えた場合。
4. **結論注入・由来混同**: 残差 ideal、空性証明、解、参加変数数などの計算結論を入力から受け取る仕様になっている場合、または観測由来を喪失している場合。
5. **復元なき真偽出力**: 解の存在・非存在のフラグだけを返し、具体的な操作式・状態表示・状態比較 $h$・語翻訳 $\tau$ への復元と元式への再評価検算を欠く場合。
6. **仕様書・テスト・ベンチの不足**: AC1〜AC7 のいずれかについて一次証拠（テスト・コマンド出力・実測ベンチ・仕様書同期）が欠けている場合、または既存 `archsig_v0.6.0` のテストが退行した場合。

---

## 実装計画（垂直スライス順）

1. **Step 1 — 中心 IR と `crates/shigure` 骨格の固定**:
   ワークスペースへ `crates/shigure` を追加し、`Presentation` / `ChangeSpec` / `EvalCondition` / 結果・沈黙型とモジュール境界を定義する。
2. **Step 2 — 多項式・ideal 計算核 (`algebra`)**:
   $\mathbb{Z}$・$\mathbb{Q}$・$\mathbb{F}_p$ 多変数多項式、単項式順序、$\mathbb{Q}$ 上の Gröbner 基底と witness 付き ideal 所属判定、Rabinowitsch 可逆条件、$\mathbb{Z}/\mathbb{Q}$ アフィン・$\mathbb{F}_p$ 全列挙、座標面支持による相互作用参加変数数（F11–F12）を実装し、代数的性質を単体・パラメトリックテストで固める。
3. **Step 3 — 意味保存・条件付き解空間・復元エンジン (`solver`)**:
   原始表示 IR から保存方程式・商環での状態 Law 閉性を生成し、$\mathcal{F}_{a,H,P}$ の計算・空性 witness・具体操作/比較射/語翻訳への復元と再評価検算を実装する。まずクレート内テストで台帳 P0–P6 と負例・沈黙を通す。
4. **Step 4 — 現行入力層 (`archsig-input`) 拡張と変換層**:
   `archsig.law/2`・`archsig.archmap/2` の最小拡張と `archsig-input → archsig-shigure` 変換層を実装し、型・参照・由来・結論注入禁止を検査する。既存全テストの非退行を確認する。
5. **Step 5 — CLI 入口・仕様書同期・代表規模ベンチ**:
   `archsig check` / `archsig run` に最小の問いと型付き出力を接続し、実バイナリ E2E で台帳通しフィクスチャと沈黙・負例を検証する。`docs/tool/archsig_v0_6_0_io/` と `README.md` を同期更新し、代表規模ベンチ（実行時間・最大 RSS）を実測する。

---

## 対象外（Non-Goals）

以下は本 PRD の対象外とし、本作業では実装・先回り設計を行わない。

- **図式補完・変更経路・合法状態の移送**（G-140 F・G: 複数 PR の可換四角形補完、一段変更の経路と Boolean 4 順序、phase 付き状態移送 $hm=\iota_D$）
- **複数解釈族の頑健判定と包含極小の追加観測**（G-140 E3–E5・G-141 D6–D7・G-142 G: 実現族 $U_b$ の 3 量化、Chevalley 層別による四分類、包含極小の分離観測列挙）
- **高次変形・syzygy 障害・Artin 試験・診断層と Atlas 比較**（G-141 E/F/G・G-142 A–F: 全 syzygy 平方零 lift 複体、Artin 試験と初回次数 $\nu$、局所 adapter の cycle 障害と SAGA/K0–K1 診断比較、値合流の Mayer–Vietoris）
- **同梱 SKILL（`tools/archsig_v0.6.0/skills/`）の拡張**および代表 OSS での SKILL 通し実測 QA
- **運用最適化の先回り実装**: キャッシュ（`--reuse` の SHIGURE 対応）、計算予算制御、配布パッケージング、細かな終了コード・エラー形式の作り込み（[Tool guideline](../tool/guideline.md#作り方) に従い、同梱 SKILL 通し実測後に検討）
- **外部手法との接続**: TLA+ モデル生成・読戻し、静的解析器からの自動取込み、ArchView / FieldSig 側の改修
- **Lean 形式化（`Formal/`）・数学本文（保護対象）・Website の変更**
- **CI への新規 job / step の恒久追加**

---

## 停止条件

次のいずれかに該当した場合、場当たり的に実装や仕様を埋めず、判断事項と根拠を整理して停止し人間へ戻す。

1. **既存入力仕様との意味衝突**: `archsig.law/2` / `archsig.archmap/2`（`semantics "archsig/0.6.0"`）の既存構文・既存意味と両立しない設計変更が必要と判明した場合。
2. **紙上証明との不整合または未定義境界**: G-139〜G-141 の紙上証明の仮定・有限還元条件・適用範囲に、仕様書未定義の設計判断が必要な境界が見つかった場合。
3. **計算量の現実的破綻**: 代表規模または台帳通しフィクスチャに対して、$\mathbb{Q}$ 上の Gröbner 基底計算が現実的な時間・メモリで収束せず、アルゴリズム選定や対象範囲の切り直しが必要になった場合。
4. **CI 時間制約への抵触**: ワークスペース全体のビルド・テストが [Tool guideline](../tool/guideline.md#ci-への追加) の想定 CI 3 分上限を超える兆候が出た場合。
