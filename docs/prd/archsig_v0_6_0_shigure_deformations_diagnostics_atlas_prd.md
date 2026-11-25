# ArchSig v0.6.0 SHIGURE 高次変形・全 syzygy 平方零 lift・Artin 試験・診断層と Atlas 比較 PRD

## 問い

既存の独立クレート `crates/shigure`（`archsig-shigure`）および `archsig.atom-definition/1`・`archsig.law/2`・`archsig.archmap/2`（`semantics "archsig/0.6.0"`）の SHIGURE 計算基盤の上で、次の 4 領域を一般の原始表示 IR と多項式・syzygy・Artin 商・有限加群コホモロジー計算核から入口（入力層・CLI）から出力（lift・修復・診断類・細分化比較・独立再評価検算・未決（`undetermined`））まで通しで成立させられるか。

1. **全 syzygy 平方零 lift・相対障害・宣言被覆比較・有限 étale 被覆 cocycle descent**（G-141 E1–E8・C8–C9・H1–H4・H10）
2. **定義的補助演算の原始消去・全局所 Artin 代数による検出次数 $\nu$・構文次数上界 $D$・一般係数の冪零商 base change**（G-141 F1–F9・H4–H7・H10）
3. **固定 label の整数診断複体 $C_\Lambda$ と係数変更・実現パラメータ上の診断層（partition 層別 $B_\pi$）・値合流の Mayer–Vietoris・診断次元実現と上半連続性反証**（G-142 A1–A3・B1–B6・C1–C4・D1–D3・W1–W2）
4. **有限連結単純グラフ上の実 adapter・SAGA / Čech 比較・制約付き全修復（$H_V, H_E$）・指定診断類 $\kappa_b$ の零性反映・Atlas 細分化（Condition C0–C6）と評価条件付き全修復 fiber 比較**（G-141 G1–G5・H8・H12 / G-142 E1–E6・F1–F7・W3）

本作業の一次仕様（target statement、受け入れ条件、失敗判定条件）はこの PRD に置く。
恒久的な I/O スキーマ、DSL 構文、標準構成規則、出力形式は実装と同期して `docs/tool/archsig_v0_6_0_io/` 配下の現行仕様書へ反映する。

---

## 現状診断と参照先

### 現状診断

- 現行の `tools/archsig_v0.6.0` は独立クレート `crates/shigure`（`archsig-shigure`）を持ち、`shigure presentation` / `comparison` / `change_spec` / `eval_condition` / `task` / `diagram` / `path` / `transfer` / `family` / `robustness` / `chevalley` / `observations` の 12 宣言と 9 種の問い（`shigure_preservation`・`shigure_solve`・`shigure_interaction`・`shigure_diagram`・`shigure_path`・`shigure_transfer`・`shigure_robustness`・`shigure_chevalley`・`shigure_observations`）を実行できる（Phase 1 `#6377`・Phase 2 `#6403`・Phase 3 `#6431` 完了済み）。
- 一方で、[全体トラッキング #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376) の Phase 4 計画（G-141 E/F/G・G-142 A–F）に相当する次の 4 領域が未実装である。
  1. **全 syzygy 平方零 lift・相対障害・局所修復比較（G-141 E1–E8・C8–C9）**: 現行 `crates/shigure/src/algebra/` には $\mathbb{Q}$ 上の Gröbner 基底・商環所属・構成可能集合演算があるが、原始多項式族 $(f_1, \dots, f_r)$ の全 syzygy 加群 $S = \ker(B^r \to J)$ の生成族計算、平方零拡大 $R' \twoheadrightarrow R$ 上の複体 $D^0 \xrightarrow{\operatorname{Jac}(f)(x)} D^1 \xrightarrow{d^1} M^q$ と障害類 $o_P \in H^1(D)$・全 lift torsor $H^0(D)$、指定観測 lift に対する相対 cone 複体 $F_u = \operatorname{Cone}(\phi)[-1]$、生 Čech total complex $T_{\mathrm{raw}}$ との比較、および有限 étale 被覆の cocycle descent（W5 の $\mu_2$-torsor 含む）を計算する構成がない。
  2. **原始消去と全 Artin 試験・検出次数 $\nu$（G-141 F1–F9）**: 定義的補助演算 $Y_j = F_j(O, Y_1, \dots, Y_{j-1})$ の依存順消去、自由観測 chart 上の構文次数上界 $D$、局所環 $A = \mathcal{O}_{M_O, a}$ における初回失敗次数 $\nu = \max\{n \mid J \subseteq \mathfrak{m}^n\}$、普遍初回拡大 $A/\mathfrak{m}^{\nu+1} \to A/\mathfrak{m}^\nu$ の相対障害 $\kappa_u$、合成則 $\nu(v \circ u) = \min\{\nu(u), \nu(v)\}$、および一般係数の冪零商 base change $D_r$ を計算する構成がない。
  3. **整数診断複体・診断層 $B_\pi$・値合流 Mayer–Vietoris・診断次元実現（G-142 A–D）**: 有限 `Source`・`Law`/`readout`・`TargetSupportedNerve` から次数 0–2 の整数・体係数診断複体 $C_\Lambda$ を生成し、固定 label 係数変更 $\Lambda \to \Lambda'$ と値域再生成を分離しつつ、多項式 readout 族上の partition 層別 $B_\pi$、値合流写像 $r_{\pi', \pi}$ の Mayer–Vietoris 長完全列（$\ker H^1(r)$・$\operatorname{coker} H^1(r)$）、および D1–D3 の診断次元実現と上半連続性反証を計算する構成がない。
  4. **有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類・Atlas 細分化 C0–C6（G-141 G・G-142 E–F）**: 有限連結単純グラフ $\Gamma = (V, E)$ 上の台帳 adapter（$p, v, i_\lambda, j_\mu, g_b$）から実残差 $r_e$・SAGA 符号比較 $T$・spanning tree 同型 $\Phi_R$・制約付き修復（$H_V, H_E$）・指定診断類 $\kappa_b$ の零性反映、および粗/細 reading と nerve 射に対する Condition C0–C6 全項目検査・評価条件付き全修復 fiber 比較を計算する構成がない。
- **肥大化停止線の現在値**（[#6376 Phase 3 引き継ぎコメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376#issuecomment-7107415912) および現ワークスペース計測）:
  - `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` への変更は Phase 1–3 を通じて 0 件を維持している。
  - 一方、`crates/input/src/law/parser.rs` は既存 **1,579 行**であり、900 行台のファイルとして `crates/shigure/src/ir/tests.rs`（986 行）・`crates/shigure/src/algebra/poly.rs`（975 行）・`crates/shigure/src/ir/tests_phase2.rs`（974 行）・`crates/shigure/src/solver/family_eval.rs`（942 行）・`crates/input/src/law/shigure/check.rs`（937 行）・`crates/shigure/src/solver/common_solve.rs`（935 行）・`crates/shigure/src/solver/restore.rs`（910 行）・`crates/input/src/law/shigure/check_relations.rs`（908 行）・`crates/shigure/src/solver/chevalley_sections.rs`（903 行）・`crates/shigure/src/solver/preservation.rs`（901 行）が存在する。Phase 4 で追記が必要になるファイルは先行分割してから拡張する。

### 参照先

| 種別 | 参照先 |
| --- | --- |
| 全体トラッキング | [GitHub Issue #6376](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376)（Phase 1 `#6377`・Phase 2 `#6403`・Phase 3 `#6431` 完了済み） |
| 編集・PRD・横断規律 | [Tool guideline](../tool/guideline.md)、[PRD guideline](guideline.md)、[Workflow guideline](../workflow/guideline.md)、[語彙ルール](../workflow/vocabulary.md) |
| 現行 I/O 仕様 | [ArchSig v0.6.0 I/O 仕様](../tool/archsig_v0_6_0_io/README.md)（[law.md](../tool/archsig_v0_6_0_io/law.md)・[computations.md](../tool/archsig_v0_6_0_io/computations.md)・[execution.md](../tool/archsig_v0_6_0_io/execution.md)・[results.md](../tool/archsig_v0_6_0_io/results.md)・[validation.md](../tool/archsig_v0_6_0_io/validation.md)）、[クレート README](../../tools/archsig_v0.6.0/README.md) |
| 設計ノート・GOAL | [n1019](../note/n1019_shigure_representability_design.md)、[n1020 §§4・13–17](../note/n1020_shigure_polynomial_specializations.md)、[n1021](../note/n1021_unified_tool_suite_rising_sea.md)、[G-141](../../research/goals/G-141-aat-coherent-repair-effectivity.md)、[G-142](../../research/goals/G-142-aat-law-value-diagnostic-sheaf.md) |
| 紙上証明（一次数学参照） | [G-141 原始 lift と相対障害](../../research/designs/G-141-aat-coherent-repair-effectivity/obstruction-complexes.md)、[G-141 全 Artin 試験](../../research/designs/G-141-aat-coherent-repair-effectivity/artin-detection.md)、[G-141 局所修復と選択](../../research/designs/G-141-aat-coherent-repair-effectivity/descent-and-selection.md)、[G-141 有限 graph 実修復](../../research/designs/G-141-aat-coherent-repair-effectivity/graph-repair.md)、[G-141 指定例 H1–H12](../../research/designs/G-141-aat-coherent-repair-effectivity/witnesses.md)、[G-142 整数診断](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/integer-diagnostics.md)、[G-142 診断の étale 層](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/diagnostic-sheaves.md)、[G-142 値の合流](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/collision-comparison.md)、[G-142 診断次元の実現](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/dimension-realization.md)、[G-142 実操作の指定障害](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/specified-obstruction.md)、[G-142 Atlas 細分化と全修復](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/atlas-refinement.md)、[G-142 指定例 W1–W6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md) |

---

## タスク固有の target statement（数学対応）

本 PRD が `crates/shigure` で有限特殊化として実装し、コード上の適用条件検査とテストで対応を検証する数学的構成は、以下の紙上証明条項に限定する。

| 対象機能 | 対応する紙上証明の条項 | 適用条件（コード上で明示検査） | 条件外時の振る舞い |
| --- | --- | --- | --- |
| 全 syzygy 平方零 lift・相対障害・宣言被覆比較・有限 étale 被覆 cocycle descent | [G-141 E1–E6](../../research/designs/G-141-aat-coherent-repair-effectivity/obstruction-complexes.md#e1--独立な実現liftとsmooth-ambient)、[E7–E8・C8–C9](../../research/designs/G-141-aat-coherent-repair-effectivity/descent-and-selection.md#e7--観測の全参照を保持する修復係数)、[H1–H4・H10](../../research/designs/G-141-aat-coherent-repair-effectivity/witnesses.md#h1--許容域が変える全修復) | 有限変数・有限個の原始多項式 Law $(f_1, \dots, f_r)$、有効な平方零拡大 $R' \twoheadrightarrow R$（$M^2 = 0$ を乗法表／商環定義で明示検査）、基点実現 $x \in \operatorname{Sem}_P(R)$ の原始 Law 充足（$f_i(x) = 0$）、syzygy 生成族計算の有効係数域（$\mathbb{Q}$ / $\mathbb{F}_p$ 上の Gröbner・Schreyer、$\mathbb{Z}$ 上の単項／線形／生成性確認済み族）と S-pair 上限内、未観測値の不在 | 評価後 Jacobian から syzygy を推定しない。$H^1(T_{\mathrm{raw}})$ と $H^1(D)$ を混同しない。$M^2 \neq 0$ や非 lawful 基点は入力／適用条件エラー。syzygy 生成性未確定・上限超過・未観測依存は `undetermined` |
| 原始消去・全 Artin 試験・初回検出次数 $\nu$・一般係数冪零商 | [G-141 F1–F9](../../research/designs/G-141-aat-coherent-repair-effectivity/artin-detection.md#定理-f1--定義的補助演算の消去)、[H4–H7・H10](../../research/designs/G-141-aat-coherent-repair-effectivity/witnesses.md#h4--二contextの差と相対障害) | Noetherian 有限表示 $O, P$、非循環の依存順を持つ定義的補助演算 $Y_j = F_j(O, Y_1, \dots, Y_{j-1})$、体 $k \in \{\mathbb{Q}, \mathbb{F}_p\}$（F8 一般係数冪零商では $\mathbb{Z} \to \mathbb{Q} / \mathbb{F}_p$ の有限商も対応）、基点 $a \in \operatorname{Sem}_P(k)$ の成立、自由観測 chart か既存関係 $I_O$ 付きかの明示区別、探索次数・S-pair 上限内 | 曲線 jet 試験 $k[t]/(t^{r+1})$ で全局所 Artin 試験を代用しない。既存関係付き表示に自由 chart の見かけの構文次数上界を主張しない。非 Noetherian 無限表示（H7）・探索次数上限超過・局所化分母判定不能は `undetermined` |
| 整数診断複体・係数変更・診断層 $B_\pi$・値合流 Mayer–Vietoris・診断次元実現 | [G-142 A1–A3](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/integer-diagnostics.md#a1--原始labelと整数微分)、[B1–B6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/diagnostic-sheaves.md#b1--独立な実現とregular-readout)、[C1–C4](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/collision-comparison.md#c1--law値別の閉じた部分複体)、[D1–D3](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/dimension-realization.md#d1--一つのlocally-closed集合)、[W1–W2](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w1--係数変更と値の再生成) | 有限 `Source`・有限 `Law`/`readout` 族・全射かつ adequate な reading（または直接の多項式 readout 族 $f_{\ell, s}$）・有限 `TargetSupportedNerve`（K1 交差支持と face 端点等式を検査）、明示された診断係数環 $\Lambda \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$、partition 数・Gröbner 層別の上限内、未観測値の不在 | 固定 label 係数変更（tensor）と値域再生成を混同しない。非 flat／非 faithful 係数変更で $H^i$ 保存や零性反映を無条件に主張しない。$B_\pi$ の幾何点分割を $R$-点（双対数等）の分割と混同しない。上限超過・非対応係数環・未観測依存は `undetermined` |
| 有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類・Atlas 細分化 C0–C6 | [G-141 G1–G5](../../research/designs/G-141-aat-coherent-repair-effectivity/graph-repair.md#g1--原始操作とadapter)、[H8・H12](../../research/designs/G-141-aat-coherent-repair-effectivity/witnesses.md#h8--三角形の全操作holonomy許容修復)、[G-142 E1–E6](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/specified-obstruction.md#e1--同じadapterとreadout)、[F1–F7](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/atlas-refinement.md#f1--有限空間の縮約と同じ空間上の二被覆)、[W3](../../research/designs/G-142-aat-law-value-diagnostic-sheaf/witnesses.md#w3--指定障害制約同じ八点空間) | 辺を 1 本以上持つ有限連結単純有向グラフ $\Gamma = (V, E)$、係数環 $R \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$、補正 readout $p(v) = 0$ と実残差 $r_e = \lambda_j - \lambda_i - b_e$ の分離、許容頂点・辺集合 $(A_V, A_E)$、細分化時は粗/細 nerve 射と Condition C0–C6 全項目の実検査、未観測値の不在 | 診断 $H^1$ の次元（一定）と指定類 $\kappa_b$ の零性を混同しない。無制約 $\kappa_b = 0$ から制約付き修復の存在を推論しない。adequacy と C0–C6 だけから評価条件付き全修復 fiber の降下を推論しない（F7）。原子操作 adapter の可換性を拡張操作言語へ自動移送しない（H12）。非連結・条件外・未観測依存は `undetermined` |

---

## 要求

### R1. 先行分割・モジュール境界維持・中心計算核と IR の先行固定

1. 既存の `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` へは新しい機能・分岐を追記せず、依存の向き `archsig-common` / `archsig-input` → `archsig-shigure` → `archsig`（CLI）を維持する。
2. [Tool guideline](../tool/guideline.md#設計と実装) の肥大化停止線および [#6376 Phase 3 引き継ぎ留意事項](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6376#issuecomment-7107415912) に従い、**Phase 4 で機能追記が必要になる 900 行台ファイル（例: `crates/input/src/law/shigure/check.rs`〔937 行〕・`check_relations.rs`〔908 行〕・`crates/shigure/src/algebra/poly.rs`〔975 行〕等）および既存 1,579 行の `crates/input/src/law/parser.rs` へ無条件に追記しない**。追記が発生するファイルは着手に先立って責務分割し、新規および実質変更対象の全 Rust ファイルを 1,000 行未満に維持する。
3. 個別の計算機能に着手する前に、次の中心データ構造・代数的計算核・検証済み IR（`Checked*`）・出力型を先に固定する。
   - **代数的計算核の拡張 (`crates/shigure/src/algebra/`)**:
     - `algebra/syzygy`: 原始多項式族 $(f_1, \dots, f_r)$ の Gröbner 基底と Schreyer 構成による全 syzygy 生成族計算（$\mathbb{Q}$ / $\mathbb{F}_p$、および $\mathbb{Z}$ の検証済み生成族）、$\sum s_i f_i = 0$ の多項式恒等式検算、および形式偏微分による Jacobian 評価。
     - `algebra/artin`: 有限次元局所 Artin 環・冪零商環 $k[\varepsilon]/(\varepsilon^{d+1})$・$k[z]/(I + \mathfrak{m}^{r+1})$・一般係数冪零商 $\mathbb{Z}[t]/(t^{r+1})$ の正確な乗法・理想商・平方零拡大 $R' \twoheadrightarrow R$（$M^2 = 0$ 検査付き）・線形代数エンジン（$\mathbb{Q}$ / $\mathbb{F}_p$ RREF および既存 $\mathbb{Z}$ Smith 標準形の再利用）。
     - `algebra/cochain`: 次数 0–2 の有限自由 $\Lambda$-加群複体 $C^0 \xrightarrow{d^0} C^1 \xrightarrow{d^1} C^2$（$\Lambda \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$）、$d^1 d^0 = 0$ 検算、$H^0, H^1, H^2$（自由階数＋$\mathbb{Z}$ torsion 不変因子・生成元基底）、指定 cocycle の類・零性判定、cochain 射による誘導写像 $H^i(f)$ の核・余核・単射・全射判定。
   - **Phase 4 中心 IR (`crates/shigure/src/ir/`)**:
     - `ir/lift`（`CheckedLiftTask`）: 原始表示または多項式 Law 系、平方零拡大 $R' \twoheadrightarrow R$ と kernel $M$、基点実現 $x$、任意の相対 reading $u: P \to P'$ と指定観測 lift $y'$、任意の宣言文脈被覆（$T_{\mathrm{raw}}$・二文脈 Čech・E7 観測支持検査）、任意の affine 許容部分加群 $H$、および任意の有限 étale 被覆・局所選択 cocycle 検査仕様。
     - `ir/artin`（`CheckedArtinTask`）: 観測表示 $O$（自由 chart / 既存関係 $I_O$ 付きの明示区別）、依存順付き定義的補助演算 $Y_j = F_j$、追加 Law $G_\alpha = 0$、基点 $a$、任意の 2 段合成 reading $u, v$、および一般係数 base change $k_0 \to k_1$ 仕様（非 Noetherian 無限表示フラグの明示区別を含む）。
     - `ir/diagnostics`（`CheckedDiagnosticsTask`）: 有限 `Source`・`Law`/`readout`・reading $q$・`TargetSupportedNerve`・診断係数環 $\Lambda$、係数変更比較 $\Lambda \to \Lambda'$（固定 label テンソル vs 値域再生成）、多項式 readout 族 $f_{\ell, s}$ による $B_\pi$ 層別・特殊化／合流比較（二値・多段）、および D1–D3 の診断次元実現仕様。
     - `ir/atlas`（`CheckedAtlasTask`）: 有限連結単純有向グラフ $\Gamma = (V, E)$・係数環 $R$・$\mu$・offset $b_e$・基準 $\lambda_i$・許容変更集合 $(A_V, A_E)$、任意の細分化仕様（粗/細 nerve 射・reading 射・評価条件 $P \hookrightarrow T$・忘却係数比較 F7）、および拡張操作言語非移送検査（H12）。
     - `ir/result_phase4`: 既存の `ShigureOutcome` 規約と一貫した型付き詳細構造（`LiftOutcomeDetail`・`ArtinOutcomeDetail`・`DiagnosticsOutcomeDetail`・`AtlasOutcomeDetail`）。

### R2. 高次変形・全 syzygy 平方零 lift・Artin 試験・診断層・Atlas 比較の計算核

既存の多項式・Gröbner・構成可能集合・線形代数計算核（`algebra`）を再利用し、直交分解を保ったうえで次の 4 計算核を構成する。

1. **全 syzygy 平方零 lift・相対障害・宣言被覆・有限 étale 被覆 descent（G-141 E1–E8・C8–C9・H1–H4・H10）**:
   - 原始多項式 Law $(f_1, \dots, f_r)$ から全 syzygy 生成族 $s^1, \dots, s^q \in \ker(B^r \to J)$ を厳密計算し、複体 $D: M^n \xrightarrow{d^0 = \operatorname{Jac}(f)(x)} M^r \xrightarrow{d^1} M^q$ の $d^1 d^0 = 0$ を検算する。ambient lift $\tilde z$ の残差 $r = f(\tilde z) \in M^r$ について $d^1 r = 0$ を確認し、障害類 $o_P = [r] \in H^1(D)$、lift 存在判定（$o_P = 0 \iff \exists \delta,\ r + d^0 \delta = 0$）、全解 torsor 基底 $H^0(D) = \ker d^0$、および存在時の実 lift $\tilde z + \delta$ の元 Law 再評価検算（`scope: "mathematical_model_reevaluation"`）を返す。
   - 冗長 Law の比較（H2: $(t^2, t^3)$ の syzygy $(t, -1)$、$\mathbb{Z}$ / $\mathbb{F}_2$ の $(z^2, 2z^2)$ の syzygy $(-2, 1)$ / $(0, 1)$）で、単一 Law との $H^0, H^1$・指定障害一致を検証する。
   - 生宣言 Čech total complex $T_{\mathrm{raw}}$（$H^1(T_{\mathrm{raw}}) \cong \operatorname{coker} d^0$）と全 syzygy 複体 $D$（$0 \to H^1(D) \to H^1(T_{\mathrm{raw}}) \to M^q$）を分離計算し、H3 の 2 系（同一基点値・同一変数支持だが syzygy $(1, 1, 1)$ の $H^1(D) = 0$ と regular sequence の $H^1(D) \cong \mathbb{Q}$・非零障害 $[-t]$）を区別する。
   - 相対 reading $u: P \to P'$ と指定観測 lift $y'$ に対し、相対 cone 複体 $F_u = \operatorname{Cone}(\phi)[-1]$（$d_F^0 \delta = (d' \delta, \phi^0 \delta)$、$d_F^1(r, e) = \phi^1 r - d e$）から相対障害 $o_u = [(r, e)] \in H^1(F_u)$ と全解 torsor $H^0(F_u) = \ker d' \cap \ker \phi^0$ を計算する。二文脈共有演算（H4: $Y = T^2 / Y = 0$、H10: $E = \mu\delta / E = 0$）で Čech 類と $o_u$・$\kappa_u$ の一致（H10 の raw read 差 $-\varepsilon^2$ は負号付き比較）を示す。
   - 局所修復被覆の観測支持条件（E7: $T \mapsto X + Y$ で $\{X\}/\{Y\}$ 分割の不適合と $\{X, Y, T\}$ 合併被覆での適合回復）、affine 許容部分加群 $H$ の修復（E6・H1）、および有限 étale 被覆の局所選択 cocycle 検査（C9・W5: $z^2 = t$ 上の $\mu_2$-cocycle と $k[t, t^{-1}]^\times$ の単元指数 $2m = 1$ 矛盾による大域 regular section 不存在）を計算する。
2. **原始消去・全 Artin 試験・初回検出次数 $\nu$・一般係数冪零商（G-141 F1–F9・H4–H7・H10）**:
   - 定義的補助演算 $Y_j = F_j(O, Y_1, \dots, Y_{j-1})$ の非循環依存順を検証し、逐次代入で残差 $\bar G_\alpha$ と消去 ideal $J_u$ を生成する（F1）。
   - 自由観測 chart 上では構文木再帰による次数上界 $D$（$J \neq 0 \implies \nu \le D$）を計算し、既存関係 $I_O \neq 0$ 付き表示では自由 chart 上界を適用しない（F7・H5）。
   - 基点 $a$ における初回失敗次数 $\nu = \max\{n \mid J \subseteq \mathfrak{m}^n\}$（$J = 0$ は $\nu = \infty$）を普遍商 $A/\mathfrak{m}^{r+1}$ 上の厳密計算で決定する（F2–F3）。出力に試験対象が全局所 Artin 代数（普遍商 $A/\mathfrak{m}^{r+1}$）であることを明記し、曲線 jet 試験 $k[t]/(t^{r+1})$ と区別する（F9）。
   - 有限 $\nu$ に対し、普遍初回拡大 $A/\mathfrak{m}^{\nu+1} \to A/\mathfrak{m}^\nu$ の相対障害 $\kappa_u: J/J^2 \to \mathfrak{m}^\nu/\mathfrak{m}^{\nu+1}$ と二文脈共有演算 Čech 差（F4–F5）を生成し、$\nu \ge 2$（どの観測 lift でも $P$-実現自体が lift 不能）と $\nu = 1$（指定観測方向のみ失敗・定値 lift 存在）を型・出力で区別する。
   - 2 段合成 reading $u, v$ の合成則 $\nu(v \circ u) = \min\{\nu(u), \nu(v)\}$（F6）、一般係数の冪零商 base change $k_0 \to k_1$ における $D_r$ の像と抽象テンソル $D_r \otimes k_1$ の比較（F8・H6: $\mathbb{Z}[t], J = (2t^2 + t^3)$ で $\mathbb{Z}/\mathbb{Q}$ は $\nu = 2$、$\mathbb{F}_2$ は $\nu = 3$、$D_2 = 2\mathbb{Z}t^2$ の像は $0$）、および非 Noetherian 無限表示（H7: $T_i = T_{i+1}^2$）での未決（`non_noetherian_infinite_presentation`）を扱う。
3. **整数診断複体・係数変更・診断層 $B_\pi$・値合流 Mayer–Vietoris・診断次元実現（G-142 A–D・W1–W2）**:
   - 有限 `Source`・`Law`/`readout`・adequate な reading・`TargetSupportedNerve`（K1 交差支持と face 端点等式を検査）から次数 0–2 の診断複体 $C_\Lambda$（$\Lambda \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$）を生成し、$H^0, H^1, H^2$（自由階数＋$\mathbb{Z}$ torsion）と Law 値別部分複体分解 $C^\bullet(\pi; \Lambda) \cong \bigoplus_{\ell, a} C^\bullet(K_a; \Lambda)$ を計算する（A1・C1）。
   - 係数変更 $\Lambda \to \Lambda'$（A2–A3・W1）では、flat 性・faithfully flat 性を明示し、固定 label テンソル（例: $\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ の $\mathbb{F}_2$ 非 flat 差、$\mathbb{Z} \to \mathbb{Q}$ での torsion 類消失）と値域再生成（例: 値 $0, 2 \in \mathbb{Z}$ の $\mathbb{F}_2$ 再評価による 2 label→1 label 合流 $a \mapsto (a, a)$）を型・出力で分離する。
   - 多項式 readout 族 $f_{\ell, s}$ に対し、全等値 partition $\pi$ の局所閉 stratum $B_\pi$ を既存 `ConstructibleSet` / `rabinowitsch_solve` で空性枝刈りして有限分割を構成し、各非空 stratum 上の定数複体 $C^\bullet(\pi; \Lambda)$・$H^i$・指定幾何点 stalk、および $R$-点（W2: $\mathbb{Q}[\varepsilon]/(\varepsilon^2)$ の $(0, 0)$ vs $(0, \varepsilon)$）の値相違と幾何点 stalk 一致の分離を返す（B1–B5・W2）。
   - 粗化 partition $\pi \to \pi'$（または特殊化 $\bar\eta \to \bar s$）に対し、単射合流 cochain 射 $r_{\pi', \pi}: C^\bullet(\pi'; \Lambda) \to C^\bullet(\pi; \Lambda)$ を生成し、二値合流の Mayer–Vietoris 長完全列から $\ker H^1(r) \cong \operatorname{coker} H^0(\rho)$（生成された類）と $\operatorname{coker} H^1(r) \cong \operatorname{im} H^1(\rho)$（消失した類）、同型判定（$H^0(\rho)$ 全射かつ $H^1(\rho) = 0$）、および多段合流の順序独立性を計算する（C2–C4・W2）。
   - D1–D2 の標準 cycle＋full 2-skeleton 構成から $V(g_1, \dots, g_r) \cap D(h)$ や有限層別関数 $\beta$ の診断次元実現を生成・検算し、特殊化 $\bar\eta \to \bar s$ で $\dim H^1(\bar\eta) > \dim H^1(\bar s)$ となる下降対が検出された場合に、上半連続性による pseudo-coherent（および perfect）な $\mathcal{O}_B$-複体非存在の有限証拠を出力する（D1–D3・W2）。
4. **有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類・Atlas 細分化 C0–C6（G-141 G・H8・H12 / G-142 E–F・W3）**:
   - 有限連結単純有向グラフ $\Gamma = (V, E)$・係数環 $R \in \{\mathbb{Z}, \mathbb{Q}, \mathbb{F}_p\}$・$\mu$・offset $b_e$・基準 $\lambda_i$ から、$d^0_\Gamma$・増加 pair 符号比較写像 $T$（$T \delta^0_{\mathrm{SAGA}} = d^0_\Gamma$ 検算）・実残差 $r_e = \lambda_j - \lambda_i - b_e$・spanning tree 同型 $\Phi_R: H^1(\Gamma; R) \xrightarrow{\sim} R^{|E| - |V| + 1}$・指定類 $o_b = [r] = [-b]$ を計算する（G1–G5）。
   - 補正 readout $p(v) = 0$（残差 $r_e$ とは独立入力）から整数／$R$／$\mathbb{Q}$ 診断複体 $C_\Lambda$ と原始 relation $[e] - [e'] = 0$ の完全性（連結性 $M \cong \mathbb{Z}$）を検算し、係数比較写像 $av \mapsto a e_{(\mathrm{Law}, 0)}$ による指定診断類 $\kappa_b$ を生成する。$H^1(C_\Lambda)$ の次元が $|E| - |V| + 1$ で offset に依存せず一定であることと、$\kappa_b = 0 \iff o_b = 0 \iff \operatorname{State}(X_\Gamma) \neq \varnothing$（$\mathbb{Z} \to \mathbb{Q}$ の零性反映含む）を分離表示する（E1–E6）。
   - 無制約の全大域操作（$H^0 \cong R$ torsor）、頂点許可集合 $H_V$ 下の修復 $d^0 a = b - d^0 \lambda$（特解・$\ker(d^0|_{H_V})$ torsor・全辺可換性再評価検算）、辺許可集合 $H_E$ 下の offset 修復 $[b] + [\Delta b] = 0$（特解・$\ker(H_E \to H^1(\Gamma; R))$ torsor ＋各解上の $H^0$ 操作自由度・再評価検算）を計算し、無制約 $\kappa_b = 0$ と制約付き修復不能を明確に区別する（G5・H8・W3）。
   - 粗/細の `TargetSupportedNerve` と `TargetSupportedNerveMorphism` に対し、**Condition C0–C6 の全 7 条件**をコード上で独立検査し、粗→細 cochain 比較写像 $p^0, p^1$（$d_f^0 p^0 = p^1 d_c^0$）・$H^0/H^1$ 同型・指定類保存 $o_f = p^1 o_c, \kappa_f = p^1 \kappa_c$・評価条件 $P \hookrightarrow T$ を含む全修復 fiber 同型 $\Phi_R: \mathcal{F}_c(R) \xrightarrow{\sim} \mathcal{F}_f(R)$ と逆復元を計算する（F1–F6・W3）。
   - 情報を落とす reading の反例比較（F7: adequacy と C0–C6 成立下で忘却係数 $t$ に対する評価 $v(t) = t$・条件 $t = 1$ が fiber 一定性を破り降下しないこと）および原子操作 adapter の拡張言語非移送（H12: $g_1$ が固定入力 apply/compact を保っても拡張 snapshot 経路や `compact_all` を保たない反例評価）を一般構成から導出する。

### R3. 現行入力層（`archsig-input`）後方互換拡張・変換層・最小 CLI 入口・判断不能の原則

1. 既存の入力版（`archsig.atom-definition/1`・`archsig.archmap/2`・`archsig.law/2`、`semantics "archsig/0.6.0"`）を維持し、予約語を増やさず文脈キーワード `shigure` の配下に Phase 4 宣言（`lift`・`artin`・`diagnostics`・`atlas` 等）を追加する。既存の通常テストおよび既存 SHIGURE Phase 1–3 テスト・フィクスチャを一切退行させない。
2. 結論注入の禁止（計算済みの syzygy 基底・$H^0/H^1/H^2$ 次元や torsion・障害類 $o_P/o_u/\kappa_u/o_b/\kappa_b$・初回検出次数 $\nu$・合流核/余核・Condition C0–C6 合否・修復解集合などの結論相当欄を Law 入力に含めた場合は構文・変換検査で exit 65 拒否）および由来分離（`OriginKind` の明示保持・欠測座標の零補完禁止）を型と検査で強制する。
3. `archsig check` / `archsig run` へ最小の 4 問いを追加する（既存の通常問いとの混在禁止・SHIGURE 問い同士の複数同時実行・`--out` への `archsig.result/4` 保存は現行 SHIGURE 経路の規約を踏襲する）。
   - `shigure_lift(<Task>)`: 全 syzygy 平方零 lift・相対 cone 障害・宣言被覆比較・有限 étale 被覆 cocycle descent
   - `shigure_artin(<Task>)`: 原始消去・構文次数上界・全 Artin 試験の検出次数 $\nu$・普遍初回障害 $\kappa_u$・一般係数冪零商 base change
   - `shigure_diagnostics(<Task>)`: 固定 label 整数診断複体・係数変更・診断層 $B_\pi$ 層別・値合流 Mayer–Vietoris・診断次元実現と上半連続性反証
   - `shigure_atlas(<Task>)`: 有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類 $\kappa_b$・Atlas 細分化 C0–C6 と全修復 fiber 比較
4. 出力には既存の `ShigureOutcome` 規約と一貫して、係数域・試験環／診断係数環の明示、由来・適用条件検査結果、復元された lift・修復・細分化逆像と `scope: "mathematical_model_reevaluation"` の独立再評価検算結果、および適用条件外・未観測依存・非 Noetherian 無限表示・計算上限超過時の理由付き `verdict: "undetermined"`（CLI では `status: "partial"`・exit 2）を保持する。

### R4. 恒久仕様書の同期更新

1. 本 PRD で導入する DSL 宣言構文、標準構成・適用条件・未決理由、CLI の問い、型付き結果スキーマ、適合例を、同じ変更の中で `docs/tool/archsig_v0_6_0_io/` 配下の恒久仕様書（[law.md](../tool/archsig_v0_6_0_io/law.md)・[computations.md](../tool/archsig_v0_6_0_io/computations.md)・[execution.md](../tool/archsig_v0_6_0_io/execution.md)・[results.md](../tool/archsig_v0_6_0_io/results.md)・[validation.md](../tool/archsig_v0_6_0_io/validation.md)、必要に応じ [inputs.md](../tool/archsig_v0_6_0_io/inputs.md)）および [tools/archsig_v0.6.0/README.md](../../tools/archsig_v0.6.0/README.md) へ反映する。

---

## 受け入れ条件（Acceptance Criteria）

| ID | 区分 | 受け入れ条件 | 確認証拠 |
| --- | --- | --- | --- |
| **AC1** | 先行分割・モジュール境界・中心核と IR 固定 | `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` への変更が 0 件であり、追記対象となる 900 行超既存ファイルが Phase 4 機能追加に先立って責務分割されている。`crates/shigure/src/algebra/`（`syzygy`・`artin`・`cochain`）・`crates/shigure/src/ir/`（Phase 4 `Checked*` と `result_phase4`）・`crates/shigure/src/solver/`・`crates/input/src/law/shigure/`・`src/run/shigure/` が独立サブモジュールとして責務分離され、新規および実質変更対象の Rust ファイルがいずれも目安 1,000 行未満に収まっている。 | 変更ファイル一覧・行数計測、依存グラフ、代数核・IR 単体テスト |
| **AC2** | 入力層後方互換拡張と入力保護 | `archsig.law/2`（`semantics "archsig/0.6.0"`）の文脈キーワード `shigure` 配下に Phase 4 宣言（`lift`・`artin`・`diagnostics`・`atlas` 等）を追加し、`archsig-input → archsig-shigure` 変換層で型・参照・由来（`OriginKind`）・係数環・平方零条件・非循環依存・nerve 端点整合を検査できる。結論注入・不正参照・由来欠落は入力／変換検査（exit 65）で拒否され、既存の全テスト・既存フィクスチャ（通常経路および Phase 1–3 SHIGURE 経路）が一切退行せず通過する。 | `cargo test --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml` 全通過、入力層・負例テスト |
| **AC3** | 全 syzygy 平方零 lift・相対障害・宣言被覆・有限 étale descent（G-141 E1–E8・C8–C9・H1–H4・H10） | 独立フィクスチャを用いた `archsig run`（`shigure_lift`）および計算核テストで次をすべて得る。(a) H1（$c + d = 1$ の全域・$\Delta d = 0$・全固定での affine 修復全解）。(b) H2（$t^2 = 0$ の二次 lift 不能と $t = 0$ との一次自由差、冗長 Law $(t^2, t^3)$ および $\mathbb{Z}/\mathbb{F}_2$ の $(z^2, 2z^2)$ の全 syzygy による $H^0/H^1$/障害一致）。(c) H3（同一基点値・同一支持の 2 系での $H^1(T_{\mathrm{raw}})$ vs $H^1(D)$ の分離: syzygy $(1,1,1)$ で $H^1(D) = 0$、$-t$ 変形で $H^1(D) \cong \mathbb{Q}$・非零障害 $[-t]$）。(d) H4・H10（相対 cone 複体 $F_u$ の非零障害 $o_u$ と二文脈共有演算 Čech 類の一致、H10 の raw read 差 $-\varepsilon^2$ の符号付き比較、および `finish_snap` での障害消滅と復元 lift の再評価一致 `reevaluation.matched = true`）。(e) E7（$T \mapsto X + Y$ の不適合被覆 $\{X\}/\{Y\}$ と合併被覆 $\{X, Y, T\}$ の対照）および C9/W5（$z^2 = t$ 上の $\mu_2$-cocycle と大域 regular section 不存在）。 | 実バイナリ E2E テスト、単体テスト、出力 JSON（syzygy・複体・障害・復元 lift 再評価検算） |
| **AC4** | 原始消去・全 Artin 試験・検出次数 $\nu$・一般係数冪零商（G-141 F1–F9・H4–H7・H10） | 独立フィクスチャを用いた `archsig run`（`shigure_artin`）および計算核テストで次をすべて得る。(a) H4（$Y = T^2, Y = 0$ で $\nu = 2$・普遍初回拡大 $k[t]/(t^3) \to k[t]/(t^2)$ と非零 $\kappa_u$）。(b) H5（$Y_1 = T^2, \dots, Y_N = 0$ で消去 ideal $(t^{2^N})$・$\nu = 2^N$・構文次数上界 $D = 2^N$ の鋭さ、および既存関係 $Y = T^N$ 付き $Y = 0$ で $\nu = N$・自由上界非適用の区別）。(c) H10（snapshot $E = \mu\delta, E = 0$ で $\nu = 2$・軸方向の全次数 lift・$\delta = \mu = \varepsilon$ の二次不能）。(d) F4 の $\nu = 1$（指定観測方向のみ失敗・定値 lift 存在）と $\nu \ge 2$（実現自体が lift 不能）の分離、および F6 合成則 $\nu(v \circ u) = \min\{\nu(u), \nu(v)\}$。(e) H6（$\mathbb{Z}[t], J = (2t^2 + t^3)$ で $\mathbb{Z}/\mathbb{Q}$ は $\nu = 2$、$\mathbb{F}_2$ は $\nu = 3$、$D_2 = 2\mathbb{Z}t^2$ の $\mathbb{F}_2$ への像が $0$）。(f) H7（非 Noetherian 無限表示 $T_i = T_{i+1}^2$ 相当入力での `non_noetherian_infinite_presentation` による未決）。 | 実バイナリ E2E テスト、単体テスト、出力 JSON |
| **AC5** | 整数診断複体・係数変更・診断層 $B_\pi$・合流 Mayer–Vietoris・次元実現（G-142 A–D・W1–W2） | 独立フィクスチャを用いた `archsig run`（`shigure_diagnostics`）および計算核テストで次をすべて得る。(a) W1（$\mathbb{Z} \xrightarrow{2} \mathbb{Z}$ の $\mathbb{F}_2$ 非 flat 差と $\mathbb{Z} \to \mathbb{Q}$ での torsion 消失、値 $0, 2 \in \mathbb{Z}$ の固定 label テンソル $\mathbb{F}_2^2$ vs $\mathbb{F}_2$ 値域再生成 $\mathbb{F}_2$ と比較射 $a \mapsto (a, a)$、三辺 cycle の $H^1(C_\mathbb{Z}) \cong \mathbb{Z}$）。(b) W2（$B = \mathbb{A}^2_{\lambda,\mu}$ 上の非空 partition 層別 $B_\pi$、全 stratum での $\dim_\Lambda H^1 = \mathbf{1}_{V(\lambda)\cap D(\mu)}$、生成 $\mu = 1, \lambda \to 0$ の $\ker H^1(r) \cong \Lambda$、消失 $\lambda = 0, \mu \to 0$ の $\operatorname{coker} H^1(r) \cong \Lambda$、双対数 $R = \mathbb{Q}[\varepsilon]/(\varepsilon^2)$ 上の $(0, 0)$ vs $(0, \varepsilon)$ の $R$-点値相違と幾何点 stalk 一致の分離、および上半連続性による pseudo-coherent 複体非存在証拠）。(c) D1–D2 の一般 $V(g_1, \dots, g_r) \cap D(h)$ 診断次元実現の検算と C2 多段合流の順序独立性。 | 実バイナリ E2E テスト、単体テスト、出力 JSON |
| **AC6** | 有限グラフ実 adapter・SAGA 比較・制約付き全修復・指定診断類・Atlas 細分化 C0–C6（G-141 G・H8・H12 / G-142 E–F・W3） | 独立フィクスチャを用いた `archsig run`（`shigure_atlas`）および計算核テストで次をすべて得る。(a) H8・W3 三角形（$b = (1, 2, -3)$ で $o_b = \kappa_b = 0$・全解 $(s, s+1, s+3)$・再評価一致、$b = (1, 0, 0)$ で非零類 $1$・大域操作空、offset 修復 $H_E$〔全辺平面／一辺単点／空〕、頂点修復 $H_V$〔無固定 1 自由度／1 固定一意／2 固定不能〕、無制約 $\kappa_b = 0$ かつ全頂点固定時の修復不能、spanning tree $\Phi_R$ による $\mathbb{Z} \to \mathbb{Q}$ 零性反映、$H^1$ 次元一定の分離）。(b) W3 八点空間の細分化で Condition C0–C6 全 7 項目の独立合格、$p^0, p^1$ と $H^1$ 同型、指定類保存 $o_f = p^1 o_c, \kappa_f = p^1 \kappa_c$、評価条件 $P \hookrightarrow T$ を含む全修復 fiber 同型 $\Phi_R$ と逆復元。(c) F7（忘却係数 $t$ による adequacy＋C0–C6 成立と評価 $v(t) = t$・条件 $t = 1$ の降下失敗の分離）および H12（原子操作 adapter $g_1$ の拡張 snapshot / `compact_all` 非移送反例）。 | 実バイナリ E2E テスト、単体テスト、出力 JSON |
| **AC7** | 判断不能の原則と代数的性質の網羅検証 | 複体条件 $d^1 d^0 = 0$、syzygy 多項式恒等式 $\sum s_i f_i = 0$、$T \delta^0_{\mathrm{SAGA}} = d^0_\Gamma$、Mayer–Vietoris 長完全列次元恒等式、多段合流順序独立性、$\nu(v \circ u) = \min\{\nu(u), \nu(v)\}$、および適用条件外（未観測座標依存、$M^2 \neq 0$、非 Noetherian 無限表示、syzygy／Artin 次数／partition 数上限超過、非連結グラフ、非対応係数環）で誤った `established` / `refuted` を返さず理由付き `undetermined`（CLI は `partial` / exit 2）を返すことを単体・パラメトリック・E2E テストで確認する。 | 代数的性質テスト、未決・負例 E2E テスト |
| **AC8** | 仕様書同期と品質確認 | 導入した DSL 宣言・標準構成・CLI 問い・出力スキーマ・適合例が `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` に同期反映されている。`rustfmt`・関連 Clippy lint・`git diff --check`・不可視／双方向制御 Unicode 検査・語彙ルール検査を通過する。 | 更新された仕様書差分、検証コマンド出力 |
| **AC9** | 代表規模ベンチマーク実測 | 数百対象・数千 Atom 級の固定代表入力（既存ベンチ入力および Phase 4 の syzygy lift・Artin 試験・診断層・Atlas 細分化を含む固定入力）について、変更前後の実行時間と最大 RSS を実測比較し、既存経路の著しい退行がなく、新規 SHIGURE 経路の計算費用が実測値として Issue / PR に記録されている。 | Issue / PR に記録した実行時間・最大 RSS の実測比較ログ |

---

## この作業での失敗判定条件（Failure Contract）

次のいずれかに該当する場合、本 PRD は未達（失敗）と判定する。

1. **肥大化停止線・境界違反**: `crates/computation/src/observed/` や `crates/input/src/law/lexer.rs` へ追記した場合、900 行超の追記対象ファイルを先行分割せずに追記した場合、または新規・実質変更対象の Rust ファイルが目安 1,000 行を超えたまま残った場合。
2. **題材固有ハードコード**: H1–H8・H10・H12・W1–W3・W5・F7 の結果を、一般の IR と syzygy／Artin 商／有限加群コホモロジー／層別計算核から導出せず、専用分岐やパターンマッチで出力した場合。
3. **数学的条件のすり替え・弱化**:
   - 原始多項式 $(f_1, \dots, f_r)$ の全 syzygy 生成族を計算せず、評価後 Jacobian や一部の関係だけで $H^1(D)$ を代替した場合、または $H^1(T_{\mathrm{raw}})$ と $H^1(D)$ を混同した場合（E2・E8・H3 違反）。
   - 曲線 jet 試験 $k[t]/(t^{r+1})$ で全局所 Artin 代数試験を代用した場合、$\nu = 1$ と $\nu \ge 2$ の lift 失敗を混同した場合、または既存関係付き表示に自由 chart の見かけの次数上界を適用した場合（F2・F4・F7・F9・H5 違反）。
   - 非 Noetherian 無限表示（H7）で全 Artin 試験一致から局所同型を主張した場合（F3・H7 違反）。
   - 固定 label 係数変更（tensor）と値域再生成を混同した場合、または非 flat／非 faithful 係数変更で $H^i$ 保存や零性反映を無条件に主張した場合（A3・W1 違反）。
   - 診断層 $B_\pi$ の幾何点分割を $R$-点（双対数等）の分割と混同した場合（B5・W2 違反）。
   - 診断 $H^1$ の次元（一定）と指定診断類 $\kappa_b$ の零性を混同した場合、または無制約 $\kappa_b = 0$ から制約付き修復（$H_V, H_E$）の存在を推論した場合（E6・G5・W3 違反）。
   - Law 値 adequacy と Condition C0–C6 による $H^1$ 同型から評価条件付き全修復 fiber の降下を推論した場合（F7 違反）、または原子操作 adapter の可換性から拡張操作言語の保存を推論した場合（H12 違反）。
4. **適用条件の無検査・未決違反・再評価検算欠落**: 係数環・平方零条件・非循環依存・Noetherian 有限表示・計算上限を検査せず条件外入力へ誤った `established` / `refuted` を返した場合、または復元した lift・修復解の独立再評価検算（`scope: "mathematical_model_reevaluation"`）を欠いた場合。
5. **結論注入・由来混同**: syzygy 基底・コホモロジー群・障害類・検出次数 $\nu$・合流核/余核・Condition C0–C6 合否・修復解などの結論相当欄を入力で受理した場合、または由来（`OriginKind`）を喪失・混同した場合。
6. **仕様書・テスト・ベンチの不足または退行**: AC1〜AC9 のいずれかの一次証拠が欠けている場合、または既存 `archsig_v0.6.0` の通常経路・Phase 1–3 SHIGURE 経路テストが退行した場合。

---

## 実装計画（垂直スライス順）

1. **Step 1 — 先行分割・代数的計算核基盤と Phase 4 中心 IR の固定**:
   Phase 4 で追記が必要になる 900 行超の既存ファイル（`check.rs`・`check_relations.rs`・`algebra/poly.rs` 等）を先に責務分割する。そのうえで `crates/shigure/src/algebra/` に独立サブモジュール（`syzygy`・`artin`・`cochain`）を実装し、`crates/shigure/src/ir/` に Phase 4 の `CheckedLiftTask`・`CheckedArtinTask`・`CheckedDiagnosticsTask`・`CheckedAtlasTask` および `result_phase4` を固定する。
2. **Step 2 — 変形・障害・Artin 試験計算核（`solver/lift`・`solver/artin`）と代数的検証**:
   全 syzygy 平方零 lift 複体 $D$・相対 cone 複体 $F_u$・$T_{\mathrm{raw}}$ 比較・E7 観測支持・C9 有限 étale 被覆 cocycle descent、および原始消去・構文次数上界 $D$・初回検出次数 $\nu$・普遍初回障害 $\kappa_u$・合成則・一般係数冪零商 $D_r$ を独立サブモジュールとして実装し、H1–H7・H10・W5・未決（`undetermined`）を単体・パラメトリックテストで通す。
3. **Step 3 — 診断層・合流・実 adapter 修復・Atlas 細分化計算核（`solver/diagnostics`・`solver/atlas`）と代数的検証**:
   整数診断複体 $C_\Lambda$・係数変更 vs 値域再生成・多項式 readout 層別 $B_\pi$・Mayer–Vietoris 合流・診断次元実現と上半連続性反証、ならびに有限グラフ実 adapter・SAGA 符号比較 $T$・spanning tree $\Phi_R$・制約付き修復（$H_V, H_E$）・指定類 $\kappa_b$・Atlas 細分化 Condition C0–C6・F7/H12 反例を実装し、W1–W3・H8・H12・D1–D3・未決（`undetermined`）を単体・パラメトリックテストで通す。
4. **Step 4 — 入力層（`archsig-input`）後方互換拡張と変換層**:
   `crates/input/src/law/shigure/` に Phase 4 宣言（`lift`・`artin`・`diagnostics`・`atlas` 等）の AST・パーサ・静的検査を独立サブモジュールとして追加し、`crates/shigure/src/convert/` の独立変換モジュールから Phase 4 の `Checked*` タスクを構築する。結論注入・由来欠落・不正参照の拒否と既存全テスト非退行を確認する。
5. **Step 5 — CLI 入口・独立フィクスチャ／E2E 検証**:
   `src/run/shigure/` に `shigure_lift`・`shigure_artin`・`shigure_diagnostics`・`shigure_atlas` を接続し、`archsig check` / `archsig run`（`--out` 保存含む）の実バイナリ E2E テストと独立 Phase 4 フィクスチャで AC3〜AC7 を検証する。
6. **Step 6 — 恒久仕様書同期・品質検査・代表規模ベンチ実測**:
   `docs/tool/archsig_v0_6_0_io/` と `tools/archsig_v0.6.0/README.md` を同期更新し、`rustfmt`・Clippy・`git diff --check`・Unicode／語彙検査・代表規模ベンチマーク（実行時間・最大 RSS の前後比較）を実施して記録する。

---

## 対象外（Non-Goals）

以下は本 PRD の対象外とし、本作業では実装・先回り設計を行わない。

- **同梱 SKILL（`tools/archsig_v0.6.0/skills/`）の SHIGURE 対応**および代表 OSS での SKILL 通し実測 QA（Phase 5 予定）
- **運用最適化の先回り実装**: キャッシュ（`--reuse` の SHIGURE 再利用対応）、計算予算制御、配布パッケージング、細かな終了コード・エラー形式の作り込み（[Tool guideline](../tool/guideline.md#作り方) に従い、同梱 SKILL 通し実測後に検討）
- **無限塔・導来逆極限 $R\varprojlim$ と 2 進完備化**（G-141 A–C の無限 adapter 列 $c_n - 2c_{n+1} = a_n$、$\lim^1(\mathbb{Z}, \times 2) \cong \mathbb{Z}_2/\mathbb{Z}$、無限 colimit 環の一般大域化）
- **一般階数（sort rank > 1）の Grassmannian 複数 chart 貼り合わせ・商 stack** および **SHIGURE 問いと通常 observed 問いの同一 `run` 混在実行**
- **外部手法との接続**: TLA+ モデル生成・読戻し（[n1020 §17.6](../note/n1020_shigure_polynomial_specializations.md#176-tlaへの対応)）、静的解析器からの自動取込み、ArchView / FieldSig 側の改修
- **Lean 形式化（`Formal/`）・数学本文（保護対象）・Website の変更**
- **CI への新規 job / step の恒久追加**

---

## 停止条件

次のいずれかに該当した場合、仮の判断で実装や仕様を埋めず、判断事項と根拠を整理して停止し人間へ戻す。

1. **既存入力仕様・既存 SHIGURE 宣言との意味衝突**: `archsig.law/2` / `archsig.archmap/2`（`semantics "archsig/0.6.0"`）の既存構文・既存 SHIGURE 12 宣言と両立しない設計変更が必要と判明した場合。
2. **紙上証明との不整合または未定義境界**: G-141 E/F/G・C8–C9 または G-142 A–F の仮定・syzygy 生成性条件・非自由観測環上の $\nu$ 計算・有限 étale 被覆 cocycle descent の扱いに、仕様書未定義の設計判断が必要な境界が見つかった場合。
3. **計算量の現実的破綻**: Schreyer 全 syzygy 計算、高次 Artin 商 $A/\mathfrak{m}^{r+1}$ の線形代数、または多項式 readout 族の全 partition $B_\pi$ 層別が代表題材で現実的な時間・メモリに収束せず、アルゴリズム選定や対象範囲の切り直しが必要になった場合。
4. **CI 時間制約への抵触**: ワークスペース全体のビルド・テストが [Tool guideline](../tool/guideline.md#ci-への追加) の想定 CI 3 分上限を超える兆候が出た場合。
