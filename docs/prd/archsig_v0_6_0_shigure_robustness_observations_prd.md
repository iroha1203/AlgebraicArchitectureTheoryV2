# ArchSig v0.6.0 SHIGURE 複数解釈族・頑健判定・包含極小の追加観測 PRD

## 問い

既存の独立クレート `crates/shigure`（`archsig-shigure`）および `archsig.atom-definition/1`・`archsig.law/2`・`archsig.archmap/2`（`semantics "archsig/0.6.0"`）の SHIGURE 計算基盤の上で、**観測と整合する複数解釈の実現族 $U \xrightarrow{q} B$ と共有規則候補族 $C \xrightarrow{\pi} B$ に対する 3 量化・全係数移送安定性・reading 比較（G-140 E3–E5・P7 / G-142 G1–G4）、評価・射影の構成可能な幾何的像と Chevalley 四分類（G-141 D6–D7 / G-142 G7）、および判定を分離するすべての包含極小な追加観測の列挙（G-142 G5–G6 / W4–W6）**を、一般の原始表示 IR と多項式／構成可能集合／有限列挙計算核から入口（入力層・CLI）から出力（witness 復元・独立再評価検算・沈黙）まで一気通貫で成立させられるか。

本作業の一次仕様（target statement、受け入れ条件、失敗判定条件）はこの PRD に置く。
恒久的な I/O スキーマ、DSL 構文、標準構成規則、出力形式は実装と同期して `docs/tool/archsig_v0_6_0_io/` 配下の現行仕様書へ反映する。

---

## 現状診断と参照先

### 現状診断

- 現行の `tools/archsig_v0.6.0` は独立クレート `crates/shigure`（`archsig-shigure`）を持ち、`shigure presentation` / `comparison` / `change_spec` / `eval_condition` / `task` / `diagram` / `path` / `transfer` の 8 宣言と 6 種の問い（`shigure_preservation`・`shigure_solve`・`shigure_interaction`・`shigure_diagram`・`shigure_path`・`shigure_transfer`）によって、意味保存変更・条件付き解空間 $\mathcal{F}_{a,H,P}$・相互作用解析・固定図式補完・一段変更経路・合法状態移送を実行できる（Phase 1 `#6377`・Phase 2 `#6403` 完了済み）。
- 一方で、[全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376) の Phase 3（G-140 E3–E5・G-141 D6–D7・G-142 G）に相当する次の 3 領域が未実装である。
  1. **複数解釈族と 3 量化・全係数移送安定性（G-140 E3–E5・E5.1・P7 / G-142 G1–G4 / [n1020 §16.9](../note/n1020_shigure_polynomial_specializations.md#reading-robustness)）**: 静的解析・実行観測・LLM 読解候補・人間採用の由来を保持したまま、同じ観測値 $b$ に整合する複数解釈を実現族 $U_b$ として保持し、直接指定型 $E_{\mathrm{dir}}$ と存在型 $E_{\mathrm{exists}}$ を区別したうえで、指定候補の頑健性（$\forall u \in U_b,\ E(u,c)$）・各実現での可解性（$\forall u \in U_b\ \exists c \in C_b,\ E(u,c)$）・共通候補の存在（$\exists c \in C_b\ \forall u \in U_b,\ E(u,c)$）・空 fiber（$U_b = \varnothing$）の分離・全係数移送で安定な全称条件 $\mathcal{R}(R)$・粗/細 reading 比較を計算する構成がない。
  2. **構成可能な幾何的像と Chevalley 四分類（G-141 D6–D7 / G-142 G7）**: 現行 `crates/shigure/src/algebra/quotient.rs` には商環 ideal 所属の有限層別があるが、射影 $v: X \to C$ の正確な構成可能像 $\bigcup_i (V(I_i) \cap D(g_i))$（消去 ideal による閉包ではなく開条件の欠損を保持した実像）、構成可能集合のブール演算（和・交わり・補集合・差）、および $P_+ = \pi(E)$・$P_- = \pi(|W| \setminus E)$ による Chevalley 四分類（$P_+ \setminus P_-$ / $P_- \setminus P_+$ / $P_+ \cap P_-$ / $C \setminus (P_+ \cup P_-)$）と witness 復元を計算する構成がない。
  3. **追加観測の kernel 条件と全包含極小十分観測の列挙（G-142 G5–G6 / [witnesses.md W4・W6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w4--共通候補と全包含極小観測)）**: 判定が混在する実現対 $\mathcal{D}_R$ に対して、追加観測候補族 $\{e_i\}_{i \in I}$ から判定 $\chi_E$ が因子分解するための kernel 条件を検査し、分離不能対の witness またはすべての包含極小な十分観測集合（最小要素数の 1 解へ潰さない全列挙と 1 要素削除反例対）を計算する構成がない。
- **肥大化停止線の現在値**: 既存 `crates/computation/src/observed/` に加え、`crates/input/src/law/shigure/check_ext_common.rs` は現在 **994 行**（目安 1,000 行まで残り 6 行）に達しており、Phase 2 完了時の引き継ぎ留意事項（[#6376 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376#issuecomment-7081280694)）のとおり、Phase 3 の機能追加に着手する前に当該ファイルを先に責務分割する必要がある。また、`crates/shigure/src/algebra/poly.rs`（975 行）・`solver/common_solve.rs`（935 行）・`solver/restore.rs`（910 行）・`input/.../check.rs`（905 行）・`solver/preservation.rs`（901 行）・`input/.../check_relations.rs`（898 行）・`input/.../parser.rs`（871 行）・`algebra/linear.rs`（868 行）・`ir/validate.rs`（861 行）も 1,000 行に近いため、[Tool guideline](../tool/guideline.md#設計と実装) に従い独立サブモジュールまたは先行分割で拡張する。

### 参照先

| 役割 | 参照先 |
| --- | --- |
| トラッキング・関連 Issue | [全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376)、[Phase 1 完了 Issue #6377](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6377)、[Phase 2 完了 Issue #6403](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6403) |
| ツール設計・品質規約 | [Tool guideline](../tool/guideline.md)、[Workflow guideline](../workflow/guideline.md)、[PRD guideline](guideline.md)、[語彙ルール](../workflow/vocabulary.md) |
| 現行 I/O・計算仕様 | [I/O 仕様](../tool/archsig_v0_6_0_io/README.md)、[Atom 定義](../tool/archsig_v0_6_0_io/definitions.md)、[ArchMap](../tool/archsig_v0_6_0_io/inputs.md)、[Law 宣言](../tool/archsig_v0_6_0_io/law.md)、[核の構成](../tool/archsig_v0_6_0_io/computations.md)、[実行](../tool/archsig_v0_6_0_io/execution.md)、[型付き結果](../tool/archsig_v0_6_0_io/results.md)、[短い適合例](../tool/archsig_v0_6_0_io/validation.md) |
| SHIGURE 構想・多項式特殊化 | [n1019（とくに §§5.6・8.3）](../note/n1019_shigure_representability_design.md)、[n1020（とくに §§16.9・17.3・17.5）](../note/n1020_shigure_polynomial_specializations.md)、[n1021（とくに §3.1）](../note/n1021_unified_tool_suite_rising_sea.md) |
| SHIGURE 紙上証明（一次数学根拠） | [G-140 目標](../../research/goals/G-140-aat-semantic-change-category.md)、[G-140 条件付き変更と共通候補（E3–E5・E5.1）](../../research/designs/G-140-aat-semantic-change-category/conditional-changes.md)、[G-140 台帳特殊化（P7）](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md)、[G-141 目標](../../research/goals/G-141-aat-coherent-repair-effectivity.md)、[G-141 有限計算（D6–D7・D8）](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md)、[G-142 目標](../../research/goals/G-142-aat-law-value-diagnostic-sheaf.md)、[G-142 観測に相対的な判定（G1–G7）](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/relative-decision.md)、[G-142 指定例（W4–W6）](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md) |
| 既存ワークスペース | `tools/archsig_v0.6.0/Cargo.toml`、`crates/input/src/law/shigure/`、`crates/shigure/`、`src/run/shigure/`、`tests/fixtures/shigure-ledger/`、`tests/fixtures/shigure-phase2/` |

---

## タスク固有の target statement（数学対応）

本 PRD が `crates/shigure` で有限特殊化として実装し、コード上の適用条件検査とテストで対応を検証する数学的構成は、以下の紙上証明条項に限定する。

| 対象機能 | 対応する紙上証明の条項 | 適用条件（コード上で明示検査） | 条件外時の振る舞い |
| --- | --- | --- | --- |
| 複数解釈族と共有規則候補族（$E_{\mathrm{dir}}$ / $E_{\mathrm{exists}}$） | [G-140 E3](../../research/designs/G-140-aat-semantic-change-category/conditional-changes.md#定義-e3--同じreading上の共有規則)、[G-142 G1](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/relative-decision.md#g1--原始実現共有規則全解) | 有限列挙可能または有限多項式表示の実現族 $U \xrightarrow{q} B$（raw 表示候補を含む）と共有候補族 $C \xrightarrow{\pi} B$、各実現候補の由来 `OriginKind` の明示、$E_{\mathrm{dir}}$（直接評価）と $E_{\mathrm{exists}}$（全解族 $\mathcal{F} \to U \times_B C$ の非空性）の明示区別、商環上の ideal 所属適用域内、未観測値の不在 | 存在判定 $E_{\mathrm{exists}}$ の真偽だけで実補完の復元を省略しない。未観測依存・商環所属適用外・有限還元不能な入力は `undetermined` |
| 指定係数域の 3 量化・非空性分離・全係数移送 $\mathcal{R}(R)$・reading 比較 | [G-140 E4–E5・E5.1](../../research/designs/G-140-aat-semantic-change-category/conditional-changes.md#定理-e4--三つの量化)、[P7](../../research/designs/G-140-aat-semantic-change-category/ledger-specialization.md#p7--型署名だけのreading)、[G-142 G2–G4](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/relative-decision.md#g2--指定rでの三つの量化)、[W4–W6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w4--共通候補と全包含極小観測) | 明示された係数域・点集合域（$\mathbb{F}_p$ / $\mathbb{Q}$ / $\mathbb{Z}$ / 代数閉包 / 全 $R$-代数 `UniversalRing`）、有限列挙または有限多項式 ideal 所属／層別による決定可能性、整合実現非空性 $U_b(R) \neq \varnothing$ の独立検査、粗/細 reading 比較 $q = r \circ q'$ の可換性 | $U_b(R) = \varnothing$ の空虚な真を頑健成立と混同しない。固定体での成立を全係数移送 $\mathcal{R}(R)$（双対数 $k[\varepsilon]/(\varepsilon^2)$ や $k[t]$ を含む）へ暗黙昇格しない。一般非線形 $\mathbb{Q}/\mathbb{Z}$ 点存在や決定不能な全称条件は `undetermined` |
| 構成可能な幾何的像と Chevalley 四分類 | [G-141 D6–D7](../../research/designs/G-141-aat-coherent-repair-effectivity/effective-solving.md#d6--評価の全fiberと構成可能な像)、[G-142 G7](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/relative-decision.md#g7--幾何点での四分類)、[W4–W6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w5--平方根の局所選択と有理点) | $\mathbb{Q}$ 上の有限型多項式表示 $U \to B \leftarrow C$（可逆条件 $D(g)$ は補助変数 $ug - 1 = 0$ で保持）または有限離散定数族、構成可能集合 $E \subseteq |U \times_B C|$（存在型では D6 による $\mathcal{F} \to U \times_B C$ の幾何的像）、層別分岐・S-pair の安全上限内 | 消去 ideal の閉包で実像を代用しない（例: $xy=1 \mapsto D(x)$）。幾何点分類を $\mathbb{Q}/\mathbb{Z}$ 点存在・大域 regular section・全係数移送 $\mathcal{R}(R)$ へ置き換えない。層別上限超過・適用外係数環は `undetermined` |
| 追加観測の kernel 条件と全包含極小十分観測の列挙 | [G-142 G5–G6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/relative-decision.md#g5--追加観測のkernel条件)、[W4・W6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w4--共通候補と全包含極小観測) | 有限列挙可能な $U_b(R)$・$C_b(R)$・候補観測添字 $I$、各追加観測 $e_i: U \to V_i$ の有効な原始評価と等号判定手続き、各 $(u,c)$ に対する停止する保存／可解性判定手続き | 最小要素数の 1 解だけに潰さず全包含極小集合を返す。$D_d = \varnothing$ の異判定対があれば観測族不足の witness を返す。Law 値 adequacy と保存判定 $\chi_E$ adequacy を混同しない。有限列挙不能・等号未決定・探索上限超過は `undetermined` |

---

## 要求

### R1. 先行分割・モジュール境界維持・中心 IR の先行固定

1. 既存の `crates/computation/src/observed/` へは新しい機能・分岐を追記せず、依存の向き `archsig-common` / `archsig-input` → `archsig-shigure` → `archsig`（CLI）を維持する。
2. [Tool guideline](../tool/guideline.md#設計と実装) の肥大化停止線および Phase 2 引き継ぎ留意事項に従い、**Phase 3 の機能追加に着手する前に `crates/input/src/law/shigure/check_ext_common.rs`（現在 994 行）を責務分割**する。また 1,000 行に近づいている既存ファイル（`algebra/poly.rs`・`solver/common_solve.rs`・`solver/restore.rs`・`input/.../check.rs`・`solver/preservation.rs`・`input/.../check_relations.rs`・`input/.../parser.rs`・`algebra/linear.rs`・`ir/validate.rs` 等）へ新機能を無条件に追記せず、独立サブモジュールとして配置し、新規および変更対象の全 Rust ファイルを 1,000 行未満に維持する。
3. 個別の計算機能に着手する前に、次の中心データ構造・中間表現（IR）・検証済み型（`Checked*`）・出力型を先に固定する。
   - **構成可能集合計算核 (`algebra/constructible`)**: 局所閉層 `LocallyClosedStratum`（$V(I) \cap D(g)$）の有限和としての `ConstructibleSet`、空性枝刈り（既存 `rabinowitsch_solve` 再利用）、ブール演算（和・交わり・補集合・差集合）、および $\mathbb{Q}$ 上の Gröbner 層別による正確な構成可能像の計算（G-141 D6）。
   - **複数解釈族・共有規則 IR (`ir/family`・`CheckedFamilySpec`)**: 実現族 $U \xrightarrow{q} B$（有限列挙型と有限多項式 scheme 型の両方、および保存検査前 raw 表示候補の明示フラグと候補ごとの `OriginKind` 由来参照）、共有規則候補族 $C \xrightarrow{\pi} B$、良否関係 $E_{\mathrm{dir}}$（直接指定型）と $E_{\mathrm{exists}}$（全解族 $\mathcal{F} \to U \times_B C$ 経由の存在型）の型レベル区別、および任意の粗/細 reading 比較 $q' \to q = r \circ q'$。
   - **頑健判定・Chevalley 四分類・追加観測タスク IR (`ir/robustness`・`ir/observation`・`CheckedRobustnessTask` / `CheckedChevalleyTask` / `CheckedObservationTask`)**: 指定係数域・点集合域、指定観測値 $b$・指定候補 $c$、全係数移送検査フラグ、追加観測候補族 $\{e_i: U \to V_i\}_{i \in I}$（任意の応用側費用 weight は包含極小判定とは分離して保持）。
   - **結果型拡張 (`ir/result_phase3`)**: 既存の `ShigureOutcome` 規約と一貫した型付き詳細構造（`RobustnessOutcomeDetail`・`ChevalleyOutcomeDetail`・`ObservationOutcomeDetail`）。整合実現非空性 witness $w$、3 量化の各判定と根拠、全係数移送 $\mathcal{R}(R)$ の結果と反証環 witness、Chevalley 4 領域の局所閉層記述と成立/不成立 witness 対、全包含極小十分観測集合と 1 要素削除反例対を保持する。

### R2. 複数解釈族・頑健判定・Chevalley 四分類・追加観測の計算核

既存の多項式・ideal 計算核（`algebra`）と意味保存・条件付き解空間・復元機構（`solver`）を再利用し、直交分解を保ったうえで次の 3 計算核を構成する。

1. **複数解釈族の 3 量化・全係数移送 $\mathcal{R}(R)$・reading 比較（G-140 E3–E5・E5.1・P7 / G-142 G1–G4・W4–W6）**:
   - 観測値 $b$ に対する整合実現 fiber $U_b(R)$ の非空性を独立に判定し、非空時は具体的な整合実現 witness $w \in U_b(R)$（および由来 `OriginKind`）を返す。$U_b(R) = \varnothing$ のときは「整合実現が空（`empty_realizations`）」として明示し、空虚な真を頑健成立と混同しない。
   - 固定係数域 $R$ 上で 3 つの量化を別個に計算して返す:
     - **指定候補の頑健性** $\operatorname{Valid}_R(c)$: $\forall u \in U_b(R),\ E_{\mathrm{ok}, R}(u, c)$（不成立時は反証実現 $u_-$ と非零残差または空性 witness を返す）
     - **各実現での可解性** $\operatorname{Pointwise}_R(b)$: $\forall u \in U_b(R)\ \exists c \in C_b(R),\ E_{\mathrm{ok}, R}(u, c)$（各 $u$ に対応する候補と witness を保持）
     - **共通候補の存在** $\operatorname{Common}_R(b)$: $\exists c \in C_b(R)\ \forall u \in U_b(R),\ E_{\mathrm{ok}, R}(u, c)$（成立時は共通候補 $c$ と各実現の witness、不成立時は反証証拠を返す）
   - 存在型 $E_{\mathrm{exists}}$ では、成立する各 $(u, c)$ に対して全解族 $\mathcal{F}_{u,c}(R)$ から実際の補完 witness（状態射 $h$・語翻訳 $\tau$・操作式等）を復元し、独立した数学モデル再評価検算（`scope: "mathematical_model_reevaluation"`）を行う。
   - **全係数移送で安定な全称条件 $\mathcal{R}(R)$ および $\mathcal{R}_{\mathrm{dec}}(R)$（E5 / G3 / W6）**: 多項式族 $U_b = \operatorname{Spec} k[u]/I_{U,b}[g^{-1}]$ と直接残差について、固定係数域での点評価と、座標環上での厳密な ideal 所属／全 $R$-代数成立を区別する。$\mathbb{F}_p$ 上の $u^p = u$（$\mathbb{F}_p$ 全点成立 vs $\mathbb{F}_p[t]$ 上 $u = t$ で反証）および台帳 finish 残差の $U' = \operatorname{Spec}\mathbb{Q}[\rho]/((\rho - 1)^2)$（$\mathbb{Q}$ 点・幾何点で全成立 vs 双対数 $\mathbb{Q}[\varepsilon]/(\varepsilon^2)$ の $\rho = 1 + \varepsilon$ で残差 $-\varepsilon \neq 0$ 反証）を一般構成から導出する。
   - **粗/細 reading 比較（E5.1 / G4 / P7）**: 細 reading $q': U \to B'$ と $q = r \circ q'$ について粗 fiber での頑健性から細 fiber での頑健性への保存を検証しつつ、単一の細 fiber からの逆向きは主張しない。台帳の型署名だけの reading $q_{\mathrm{type}}$（P7）で同じ像を持つ旧 finish と `finish_snap` が異なる保存残差（$-1$ vs $0$）を持つことを原始式から計算し、存在しない合法実行を測ったことにしない。
2. **構成可能な幾何的像（G-141 D6）と Chevalley 四分類（G-141 D7・G-142 G7・W4–W6）**:
   - $\mathbb{Q}$ 上の有限多項式系 $v: X \to C$（可逆条件 $D(g)$ は補助変数 $ug - 1 = 0$ で保持）に対し、parameter 空間 $C$ 上の先頭係数零化／可逆分岐による Gröbner 層別（D6）で、各局所閉層上の fiber Gröbner 基底が $1$ を含むか否かを決定し、閉包（消去 ideal）ではなく正確な構成可能像 $\bigcup_i (V(I_i) \cap D(g_i))$ を計算する（例: $xy = 1$ の $x$ への像は閉包 $\mathbb{A}^1$ ではなく $D(x)$）。
   - $W = U \times_B C$・射影 $\pi: W \to C$・構成可能集合 $E \subseteq |W|$（存在型では全解 family $\mathcal{F} \to W$ の幾何的像を D6 で先に計算）に対して $P_+ = \pi(E)$・$P_- = \pi(|W| \setminus E)$ を構成可能集合として計算し、互いに素で全候補を尽くす Chevalley 四分類を出力する:
     - `robust_all_pass`（$P_+ \setminus P_-$）
     - `all_fail`（$P_- \setminus P_+$）
     - `mixed`（$P_+ \cap P_-$）— 指定候補または代表点に対し、成立実現 $u_+$（＋存在型なら補完 witness）と不成立実現 $u_-$（＋空性 witness または非零残差）の対を返す
     - `empty_realizations`（$C \setminus (P_+ \cup P_-)$）
   - 出力には必ず `point_domain: "algebraic_closure"` を明示し、幾何点分類を有理点存在（W5: $z^2 = t$ の $t = 2$ 上の有理点 fiber は空）・大域 regular section 存在（W5: $k[t, t^{-1}]$ 上の単元指数 $2n = 1$ 矛盾）・全係数移送 $\mathcal{R}(R)$（W6: $(\rho - 1)^2 = 0$ の $\rho = 1 + \varepsilon$）へ黙って置き換えない。
3. **追加観測の kernel 条件と全包含極小十分観測の列挙（G-142 G5–G6・W4・W6）**:
   - 有限列挙可能な $U_b(R)$・$C_b(R)$・候補観測族 $\{e_i: U \to V_i\}_{i \in I}$ について、原始評価から異判定対 $\mathcal{D}_R = \{(u, u', c) \mid q(u) = q(u') = \pi(c),\ \chi_E(u, c) \neq \chi_E(u', c)\}$ と各対の分離添字集合 $D_d = \{i \in I \mid e_i(u) \neq e_i(u')\}$ を生成する。
   - $D_d = \varnothing$ となる異判定対が存在する場合は、宣言済み観測族の不足を示す witness として当該 $(u, u', c)$ と全観測値一致の証拠を返し、判定を `refuted` とする。
   - $\mathcal{D}_R = \varnothing$ の場合は空集合 $\varnothing$ を唯一の包含極小十分集合として返す。
   - それ以外では最小要素数の 1 解へ絞らず、すべての包含極小な十分観測集合 $J \subseteq I$（すべての $D_d$ と交わり、任意の $j \in J$ に対して $J \setminus \{j\}$ が不十分となる全集合）を過不足なく列挙し、各 $J$ と各 $j \in J$ について $J \setminus \{j\}$ の不十分性を示す異判定対の witness を出力する。
   - 元の Law readout に対する adequacy と、保存判定 $\chi_E$ に対する adequacy を区別して扱えること（W6: 定数 readout に対して粗 reading が adequate でも、保存判定 $\chi_E$ は $e(\rho) = \rho$ なしでは分離不能）。
   - 各観測候補に任意の応用側費用（cost）が指定されている場合は、すべての包含極小な十分集合を求めたうえで、それらの間で費用比較・順位付けした要約を併記する（包含極小の全列挙自体を費用最小 1 解へ置き換えない）。

### R3. 現行入力層（`archsig-input`）後方互換拡張・変換層・最小 CLI 入口・沈黙規律

1. 既存の入力版（`archsig.atom-definition/1`・`archsig.archmap/2`・`archsig.law/2`、`semantics "archsig/0.6.0"`）を維持し、予約語を増やさず文脈キーワード `shigure` の配下に複数解釈族・頑健判定・Chevalley 四分類・追加観測の最小宣言（`family`・`robustness`・`chevalley`・`observations` 等）を追加する。既存の通常テストおよび既存 SHIGURE Phase 1・Phase 2 テスト・フィクスチャを一切退行させない。
2. 結論注入の禁止（計算済み 3 量化結果、Chevalley 四分類ラベル、$P_+$/$P_-$ 集合、異判定対、包含極小観測集合、十分性真偽、反証 witness などの結論相当欄を Law 入力に含めた場合は構文・変換検査で exit 65 拒否）および由来分離（候補解釈ごとの `OriginKind` の明示保持、LLM 読解候補と静的解析／実行観測／人間採用の非混同、欠測座標の零補完禁止）を型と検査で強制する。
3. `archsig check` / `archsig run` へ最小の 3 問いを追加する（既存の通常問いとの混在禁止・SHIGURE 問い同士の複数同時実行・`--out` への `archsig.result/4` 保存は現行 SHIGURE 経路の規約を踏襲する）。
   - `shigure_robustness(<Task>)`: 複数解釈族上の 3 量化・非空性分離・全係数移送 $\mathcal{R}(R)$・粗/細 reading 比較
   - `shigure_chevalley(<Task>)`: 構成可能な幾何的像（D6）および Chevalley 四分類（D7・G7）
   - `shigure_observations(<Task>)`: 追加観測の kernel 条件検査と全包含極小十分観測集合の列挙（G5–G6）
4. 出力には既存の `ShigureOutcome` 規約と一貫して、係数域・点集合域の明示、由来・適用条件検査結果、復元された witness と `scope: "mathematical_model_reevaluation"` の独立再評価検算結果、および適用条件外・未観測依存・層別上限超過・有限列挙上限超過・非線形 $\mathbb{Q}/\mathbb{Z}$ 存在判定・未決定等号時の理由付き `verdict: "undetermined"`（CLI では `status: "partial"`・exit 2）を保持する。

### R4. 恒久仕様書の同期更新

1. 本 PRD で導入する DSL 宣言構文、標準構成・適用条件・沈黙理由、CLI の問い、型付き結果スキーマ、適合例を、同じ変更の中で `docs/tool/archsig_v0_6_0_io/` 配下の恒久仕様書（[law.md](../tool/archsig_v0_6_0_io/law.md)・[computations.md](../tool/archsig_v0_6_0_io/computations.md)・[execution.md](../tool/archsig_v0_6_0_io/execution.md)・[results.md](../tool/archsig_v0_6_0_io/results.md)・[validation.md](../tool/archsig_v0_6_0_io/validation.md)、必要に応じ [inputs.md](../tool/archsig_v0_6_0_io/inputs.md)）および [tools/archsig_v0.6.0/README.md](../../tools/archsig_v0.6.0/README.md) へ反映する。

---

## 受け入れ条件（Acceptance Criteria）

| ID | 区分 | 受け入れ条件 | 確認証拠 |
| --- | --- | --- | --- |
| **AC1** | 先行分割・モジュール境界・IR 固定 | `crates/computation/src/observed/` への変更が 0 件であり、`crates/input/src/law/shigure/check_ext_common.rs` が Phase 3 機能追加に先立って責務分割されている。`crates/shigure`・`crates/input/src/law/shigure/`・`src/run/shigure/` の構成可能集合・複数解釈族・頑健判定・Chevalley 四分類・追加観測の IR（`Checked*` 含む）・計算核・変換層・CLI 入口が独立サブモジュールとして責務分離され、新規および変更対象の Rust ファイルがいずれも目安 1,000 行未満に収まっている。 | 変更ファイル一覧・行数計測、依存グラフ、IR 単体テスト |
| **AC2** | 入力層後方互換拡張と入力保護 | `archsig.law/2`（`semantics "archsig/0.6.0"`）の文脈キーワード `shigure` 配下に複数解釈族・頑健判定・Chevalley 四分類・追加観測の宣言を追加し、`archsig-input → archsig-shigure` 変換層で型・参照・由来（`OriginKind`）・係数域・点集合域整合を検査できる。結論注入・意味 Law 編集・不正参照・由来欠落は入力／変換検査（exit 65）で拒否され、既存の全テスト・既存フィクスチャ（通常経路および Phase 1・Phase 2 SHIGURE 経路）が一切退行せず通過する。 | `cargo test --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml` 全通過、入力層・負例テスト |
| **AC3** | 複数解釈族・3 量化・全係数移送・reading 比較（G-140 E3–E5・P7 / G-142 G1–G4・W4–W6） | 独立フィクスチャを用いた `archsig run`（`shigure_robustness`）および計算核テストで次をすべて得る。(a) W4（$U_b = C_b = \{0, 1\},\ E(u,c) \iff u = c$）で `Pointwise` 成立・`Common` 不成立・指定候補混在を区別。(b) 空 fiber $U_b(R) = \varnothing$ を「整合実現が空」として返し、空虚な真を頑健成立と混同しない。(c) 存在型 $E_{\mathrm{exists}}$ で成立時の補完 witness 復元・再評価一致（`reevaluation.matched = true`）と不成立時の空性 witness または非零残差を返す。(d) 全係数移送 $\mathcal{R}(R)$ の分離: $\mathbb{F}_p$ 上 $u^p = u$（$\mathbb{F}_p$ 点全成立 vs $\mathbb{F}_p[t]$ 上 $u = t$ 反証）および W6 の $U' = \operatorname{Spec}\mathbb{Q}[\rho]/((\rho-1)^2)$（$\mathbb{Q}$ 点・幾何点全成立 vs 双対数 $\mathbb{Q}[\varepsilon]/(\varepsilon^2)$ の $\rho = 1 + \varepsilon$ 反証）。(e) 粗/細 reading 比較（粗での頑健性から細への保存）および P7 の型署名だけ reading $q_{\mathrm{type}}$ での 2 候補残差差（$-1$ vs $0$）の導出。 | 実バイナリ E2E テスト、単体テスト、出力 JSON（3 量化・非空 witness・$\mathcal{R}(R)$ 反証 witness・再評価検算） |
| **AC4** | 構成可能像と Chevalley 四分類（G-141 D6–D7 / G-142 G7・W4–W6） | 独立フィクスチャを用いた `archsig run`（`shigure_chevalley`）および計算核テストで次をすべて得る。(a) D6 の $xy = 1$ の $x$ への射影で、消去 ideal の閉包 $\mathbb{A}^1$ ではなく正確な構成可能像 $D(x)$ を返す。(b) Chevalley 四分類の全 4 区分（`robust_all_pass` $P_+ \setminus P_-$ / `all_fail` $P_- \setminus P_+$ / `mixed` $P_+ \cap P_-$ / `empty_realizations` $C \setminus (P_+ \cup P_-)$）を計算し、`mixed` では成立実現 $u_+$（＋存在型なら補完 witness）と不成立実現 $u_-$（＋空性 witness または非零残差）の対を返す。(c) W5（$z^2 = t$ on $\mathbb{G}_m$）で、各固定候補 $z_0$ が `mixed`、存在型投影が幾何点で全 $\mathbb{G}_m$ 非空である一方、$t = 2$ の有理点 fiber が空であることおよび大域 regular section の不存在を幾何点分類と区別して返す。(d) W6 の $U' = \operatorname{Spec}\mathbb{Q}[\rho]/((\rho-1)^2)$ で幾何点分類 `robust_all_pass` と全係数移送 $\mathcal{R}(\mathbb{Q})$ 反証を混同しない。 | 実バイナリ E2E テスト、構成可能集合単体テスト、出力 JSON |
| **AC5** | 追加観測の kernel 条件と全包含極小十分観測（G-142 G5–G6・W4・W6） | 独立フィクスチャを用いた `archsig run`（`shigure_observations`）および計算核テストで次をすべて得る。(a) W4（$U = \mathbb{F}_2^2,\ E(u,0) \iff u_1 = 0,\ e_1 = u_1,\ e_2 = u_2,\ e_3 = u_1 + u_2$）で最小要素数へ潰さず `{e1}` と `{e2, e3}` の両包含極小十分集合と各 1 要素削除反例対を返す。(b) $D_d = \varnothing$ の異判定対に対する観測族不足 witness（`refuted`）。(c) $\mathcal{D}_R = \varnothing$ に対する空集合 $\varnothing$ 唯一の包含極小解。(d) W6 の定数 Law readout（粗 reading adequate）と保存判定 $\chi_E$（不十分・$e(\rho) = \rho$ で分離）の対照例。(e) 応用側費用（cost）指定時に全包含極小集合を保持したまま費用順比較できること。 | 実バイナリ E2E テスト、単体・パラメトリックテスト、出力 JSON |
| **AC6** | 沈黙規律と代数的性質の網羅検証 | 構成可能集合ブール演算の法則、Chevalley 4 領域の互いに素性と全被覆性、包含極小集合の十分性・極小性（全 1 要素除去の不十分性）、係数域・点集合域の区別、および適用条件外（未観測座標依存、非線形 $\mathbb{Q}/\mathbb{Z}$ 点存在判定、層別分岐・S-pair 上限超過、有限列挙・観測候補数上限超過、有限還元不能な入力）で誤った `established` / `refuted` を返さず理由付き `undetermined`（CLI は `partial` / exit 2）を返すことを単体・パラメトリック・E2E テストで確認する。 | 代数的性質テスト、沈黙・負例 E2E テスト |
| **AC7** | 仕様書同期と品質確認 | 導入した DSL 宣言・標準構成・CLI 問い・出力スキーマ・適合例が `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` に同期反映されている。`rustfmt`・関連 Clippy lint・`git diff --check`・不可視／双方向制御 Unicode 検査・語彙ルール検査を通過する。 | 更新された仕様書差分、検証コマンド出力 |
| **AC8** | 代表規模ベンチマーク実測 | 数百対象・数千 Atom 級の固定代表入力（既存ベンチ入力および Phase 3 の複数解釈族・Chevalley 分類・追加観測を含む固定入力）について、変更前後の実行時間と最大 RSS を実測比較し、既存経路の著しい退行がなく、新規 SHIGURE 経路の計算費用が実測値として Issue / PR に記録されている。 | Issue / PR に記録した実行時間・最大 RSS の実測比較ログ |

---

## この作業での失敗判定条件（Failure Contract）

次のいずれかに該当する場合、本 PRD は未達（失敗）と判定する。

1. **肥大化停止線・境界違反**: `crates/computation/src/observed/` へ追記した場合、`check_ext_common.rs` を先行分割せずに追記した場合、または目安 1,000 行を超えるファイルへ責務分割なしに実装を継ぎ足した場合。
2. **題材固有ハードコード**: W4（`{e1}`・`{e2, e3}`）・W5（$z^2 = t$）・W6（$(\rho - 1)^2 = 0$ と $\rho = 1 + \varepsilon$）・P7（$q_{\mathrm{type}}$）・$xy = 1 \mapsto D(x)$ を、一般の IR と構成可能集合／多項式／有限列挙計算核から導出せず、専用分岐やパターンマッチで出力した場合。
3. **数学的条件のすり替え・弱化**:
   - $U_b(R) = \varnothing$ の空虚な真を「整合実現が存在し頑健に成立した」と報告した場合（E4・G2 違反）。
   - `Pointwise`（$\forall u \exists c$）と `Common`（$\exists c \forall u$）を混同した場合、または `Pointwise` から大域 regular section の存在を主張した場合（E4・G4・W5 違反）。
   - 固定係数域での全称成立 $\operatorname{Valid}_R(c)$ や幾何点での全成立を、全係数移送で安定な全称条件 $\mathcal{R}(R)$ と混同した場合（E5・G3・W6 違反）。
   - 射影の構成可能像を消去 ideal の閉包で代用した場合（D6 違反: 例 $xy = 1$ を $\mathbb{A}^1$ と返す）。
   - Chevalley の幾何点分類を有理点・整数点存在判定と混同した場合（D7・G7・W5 違反）。
   - 包含極小の追加観測列挙を最小要素数（または最小費用）の 1 解だけに潰した場合、または Law 値 adequacy から保存判定 $\chi_E$ の adequacy を推論した場合（G5・G6・W4・W6 違反）。
   - 存在型 $E_{\mathrm{exists}}$ で真偽のみを返し、全解族 $\mathcal{F}_{u,c}$ からの実補完 witness 復元と独立再評価検算を欠いた場合（E3・G1 違反）。
4. **適用条件の無検査・沈黙違反・係数域混同**: 係数域・点集合域・有限還元条件・層別上限を検査せず、条件外入力に対して誤った `established` / `refuted` や暗黙の近似を返した場合。
5. **結論注入・由来混同**: 3 量化結果・Chevalley 四分類・異判定対・包含極小集合などの結論相当欄を入力で受理した場合、または複数解釈候補の由来（`OriginKind`: 静的解析・実行観測・LLM 読解候補・人間採用）を喪失・混同した場合。
6. **仕様書・テスト・ベンチの不足または退行**: AC1〜AC8 のいずれかの一次証拠が欠けている場合、または既存 `archsig_v0.6.0` の通常経路・Phase 1・Phase 2 SHIGURE 経路テストが退行した場合。

---

## 実装計画（垂直スライス順）

1. **Step 1 — 先行分割・構成可能集合核と Phase 3 中心 IR の固定**:
   `crates/input/src/law/shigure/check_ext_common.rs` を先に責務分割して 1,000 行未満に余裕を確保する。そのうえで `crates/shigure/src/algebra/constructible.rs`（局所閉層・ブール演算・D6 Gröbner 層別による構成可能像）と、`crates/shigure/src/ir/` の独立サブモジュール（複数解釈族・共有規則・頑健判定・Chevalley 四分類・追加観測の `Checked*` IR および結果型拡張）を固定する。
2. **Step 2 — 計算核（頑健判定・Chevalley 四分類・包含極小追加観測）と代数的検証**:
   `crates/shigure/src/solver/` に独立サブモジュール（`robustness`・`chevalley`・`observation`）を実装し、既存の `algebra`・`preservation`・`solve`・`restore` を再利用して E3–E5・P7・D6–D7・G1–G7 を構成する。クレート内の単体・パラメトリックテストで W4–W6・P7・$xy = 1 \mapsto D(x)$・空 fiber・全係数移送 $\mathcal{R}(R)$・沈黙を通す。
3. **Step 3 — 入力層（`archsig-input`）後方互換拡張と変換層**:
   `crates/input/src/law/shigure/` に複数解釈族・頑健判定・Chevalley 四分類・追加観測宣言の AST・パーサ・静的検査を独立サブモジュールとして追加し、`crates/shigure/src/convert/` の独立変換モジュールから `CheckedRobustnessTask` / `CheckedChevalleyTask` / `CheckedObservationTask` を構築する。結論注入・由来欠落・不正参照の拒否と既存全テスト非退行を確認する。
4. **Step 4 — CLI 入口・独立フィクスチャ／E2E 検証**:
   `src/run/shigure/` に `shigure_robustness`・`shigure_chevalley`・`shigure_observations` を接続し、`archsig check` / `archsig run`（`--out` 保存含む）の実バイナリ E2E テストと独立 Phase 3 フィクスチャで AC3〜AC6 を検証する。
5. **Step 5 — 恒久仕様書同期・品質検査・代表規模ベンチ実測**:
   `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` を同期更新し、`rustfmt`・Clippy・`git diff --check`・Unicode／語彙検査・代表規模ベンチマーク（実行時間・最大 RSS の前後比較）を実施して記録する。

---

## 対象外（Non-Goals）

以下は本 PRD の対象外とし、本作業では実装・先回り設計を行わない。

- **高次変形・全 syzygy 平方零 lift・Artin 試験・診断層と Atlas 比較**（Phase 4 予定: G-141 E/F/G・G-142 A–F — 全 syzygy 平方零 lift 複体、初回次数 $\nu$ の Artin 試験、局所 adapter の cycle 障害と SAGA / K0–K1 診断比較、値合流の Mayer–Vietoris、一般の有限 étale 被覆 cocycle descent）
- **同梱 SKILL（`tools/archsig_v0.6.0/skills/`）の SHIGURE 対応**および代表 OSS での SKILL 通し実測 QA（Phase 5 予定）
- **運用最適化の先回り実装**: キャッシュ（`--reuse` の SHIGURE 再利用対応）、計算予算制御、配布パッケージング、細かな終了コード・エラー形式の作り込み（[Tool guideline](../tool/guideline.md#作り方) に従い、同梱 SKILL 通し実測後に検討）
- **一般階数（sort rank > 1）の複数 chart 貼り合わせ・商 stack** および **SHIGURE 問いと通常 observed 問いの同一 `run` 混在実行**
- **外部手法との接続**: TLA+ モデル生成・読戻し（[n1020 §17.6](../note/n1020_shigure_polynomial_specializations.md#176-tlaへの対応)）、静的解析器からの自動取込み、ArchView / FieldSig 側の改修
- **Lean 形式化（`Formal/`）・数学本文（保護対象）・Website の変更**
- **CI への新規 job / step の恒久追加**

---

## 停止条件

次のいずれかに該当した場合、場当たり的に実装や仕様を埋めず、判断事項と根拠を整理して停止し人間へ戻す。

1. **既存入力仕様・既存 SHIGURE 宣言との意味衝突**: `archsig.law/2` / `archsig.archmap/2`（`semantics "archsig/0.6.0"`）の既存構文・既存 SHIGURE 8 宣言（`presentation` / `comparison` / `change_spec` / `eval_condition` / `task` / `diagram` / `path` / `transfer`）と両立しない設計変更が必要と判明した場合。
2. **紙上証明との不整合または未定義境界**: G-140 E3–E5、G-141 D6–D7、または G-142 G の仮定・有限還元条件・存在型 $E_{\mathrm{exists}}$ の witness 復元・全係数移送 $\mathcal{R}(R)$ の扱いに、仕様書未定義の設計判断が必要な境界が見つかった場合。
3. **計算量の現実的破綻**: Chevalley 層別における Gröbner 基底分岐、または包含極小追加観測の $2^{|I|}$ 列挙が代表題材で現実的な時間・メモリに収束せず、アルゴリズム選定や対象範囲の切り直しが必要になった場合。
4. **CI 時間制約への抵触**: ワークスペース全体のビルド・テストが [Tool guideline](../tool/guideline.md#ci-への追加) の想定 CI 3 分上限を超える兆候が出た場合。
