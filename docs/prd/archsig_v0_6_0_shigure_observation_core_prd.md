# ArchSig v0.6.0 SHIGURE Phase 5 PRD: AAT 第VI部（第17〜19章）観測コアの垂直スライス

## 問い

実コードから得る観測には、同名出現の曖昧さ、欠測と明示不在の混在、リポジトリの一部しか読めない開領域、複数ソース間の矛盾、およびコード変更に伴う観測の改訂が常に伴う。
ArchSig v0.6.0 の既存 3 入力形式（`archsig.atom-definition/1`・`archsig.law/2`・`archsig.archmap/2`、`semantics "archsig/0.6.0"`）と独立クレート境界（`crates/shigure`）を維持したまま、AAT 数学本文 第VI部 第17〜19章の有限構成を計算核として導入することで、次をどこまで機械的かつ根拠付きで計算できるか。

1. 原始出現の同一視要求と操作・評価文脈から、最小機能閉包・衝突の有限導出列・最粗の健全な商・必要な最小補助属性値域を導出できるか（第17章）。
2. 明示不在と未観測を分離した部分提示から、補完の整合性と極小不整合抽出、強 Kleene 三値評価と超評価／アフィン正規化、解の量化 4 階層（$E / U / G / Q$）と必要スロット、および開領域における局所網羅による Law 評価一致を判定できるか（第18章）。
3. 観測の追記と改訂スパンに対して、構造制約から作る意味的無効化錐 $\operatorname{Cone}(\Delta)$ と錐外不変性、作用素と右辺を分離した SNF（単因子標準形）修復再利用、多源提示の高次構造衝突の極小列挙、および検証後に結論を支える最小由来支持を計算できるか（第19章）。

本作業の target statement と受け入れ条件はこの PRD に置く。

## 現状診断と参照先

### 現状の実装と境界

- 全体トラッキング Issue #6376 の Phase 1〜4（#6377・#6403・#6431・#6479）が完了し、`tools/archsig_v0.6.0/crates/shigure` に 13 種別の SHIGURE 問い（`shigure_preservation`・`shigure_solve`・`shigure_interaction`・`shigure_diagram`・`shigure_path`・`shigure_transfer`・`shigure_robustness`・`shigure_chevalley`・`shigure_observations`・`shigure_lift`・`shigure_artin`・`shigure_diagnostics`・`shigure_atlas`）が実装済みである。
- 現行の Phase 1〜4 SHIGURE 計算核は完全観測を前提としており、未観測座標が 1 件でも含まれる場合は `undetermined`（`unobserved_dependency`）を返す設計になっている。
- 一方、次期 Phase 6（旧 Phase 5: 同梱 SKILL 統合・代表 OSS 通し実測 QA）では、実コードに対する LLM 読解・静的解析・仕様照合を束ねる必要があり、出現同定・部分提示・開領域評価・改訂無効化・多源衝突・最小由来支持を計算核側で支える基盤が不足している。
- 既存の `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` は肥大化停止線の対象であり、Phase 5 でも一切追記しない。また、`crates/input/src/law/parser.rs`（1,579 行）・`crates/input/src/law/expr.rs`（1,839 行）・`crates/input/src/law/shigure/parser_phase4_lift_artin.rs`（965 行）等の大規模ファイルへ機能を積み増さず、独立サブモジュールへ分離して実装する。

### 参照する恒久文書・Issue

| 対象 | 参照先 |
| --- | --- |
| 全体トラッキングと Phase 依存順 | GitHub Issue #6376（完了済み子 Issue: #6377・#6403・#6431・#6479） |
| 数学本文 第17章（出現の同定と観測語彙） | [chapter_17_occurrence_identity_and_observation_vocabulary.md](../aat/algebraic_geometric_theory/part_6/chapter_17_occurrence_identity_and_observation_vocabulary.md) |
| 数学本文 第18章（部分提示・欠測と開領域の確定評価） | [chapter_18_partial_presentations_and_open_domains.md](../aat/algebraic_geometric_theory/part_6/chapter_18_partial_presentations_and_open_domains.md) |
| 数学本文 第19章（観測の改訂・無効化範囲と多源統合） | [chapter_19_observation_revision_and_source_integration.md](../aat/algebraic_geometric_theory/part_6/chapter_19_observation_revision_and_source_integration.md) |
| 製品コンセプト | [archsig_v0_6_0_concept.md](../tool/archsig_v0_6_0_concept.md) |
| ツール編集ガイドライン・Rust 品質・肥大化停止線 | [docs/tool/guideline.md](../tool/guideline.md) |
| 横断作業規律・語彙ルール | [docs/workflow/guideline.md](../workflow/guideline.md)、[docs/workflow/vocabulary.md](../workflow/vocabulary.md) |
| ArchSig v0.6.0 恒久 I/O 仕様 | [docs/tool/archsig_v0_6_0_io/README.md](../tool/archsig_v0_6_0_io/README.md)（`law.md`・`computations.md`・`execution.md`・`results.md`・`validation.md`） |
| ArchSig v0.6.0 実装構成 | [tools/archsig_v0.6.0/README.md](../../tools/archsig_v0.6.0/README.md) |

## Target Statement

ArchSig v0.6.0 の独立クレート `archsig-shigure`・入力層 `archsig-input`・CLI 入口 `src/run/shigure/` へ、AAT 第VI部 第17〜19章の有限計算核に対応する 4 種別の宣言および問い（`shigure_occurrence`・`shigure_partial`・`shigure_revision`・`shigure_multisource`）を垂直スライスとして追加する。

- 既存 3 入力形式・既存通常経路・Phase 1〜4 の 13 種別の SHIGURE 問いを一切退行させず、同一 `archsig run` 内で他の SHIGURE 問いと並べて実行できる。
- 各計算は数学本文の定理・命題の適用条件（有限性・補完非空性・設定 17.5 の文脈閉性・必須 Law の補完非混入・開領域の局所網羅・作用素不変性・計算上限）をコード上で明示検査し、条件外入力には誤った `established` / `refuted` を返さず、理由コード付きの `undetermined`（CLI `status: "partial"`, exit 2）を返す。
- すべての観測項目・源・候補記録は `OriginKind`（`static_analysis`・`runtime_observation`・`llm_candidate`・`human_adopted`）およびソース参照を保持し、計算結論の外部入力（結論注入）を構文・変換検査（exit 65）で拒否する。

## 要求

### 1. モジュール境界と IR 先決め

- `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` への変更は 0 件を維持する。
- 新規および実質変更するすべての Rust ファイルを 1,000 行未満に保つ。900 行超の既存ファイルへ追記が必要になる場合は、機能追加に先立って責務分割を行う。
- 表現を先に固定し、`crates/shigure` 内に Phase 5 専用の独立モジュール境界を設ける。
  - **代数的・離散計算核（`crates/shigure/src/algebra/`）**: 導出列付き機能閉包（congruence closure）、反復細分（partition refinement）と分離文脈生成、最小横断集合（極小ヒット集合）列挙、整数 Smith Normal Form（$UMV = D$、単因子と可逆変換行列の保持・再利用）。
  - **検証済み IR（`crates/shigure/src/ir/`）**: `CheckedOccurrenceTask`・`CheckedPartialTask`・`CheckedRevisionTask`・`CheckedMultisourceTask`、および型付き結果詳細（`result_phase5.rs`）。既知値・明示不在・未観測スロットを型で明確に区別する。
  - **計算核（`crates/shigure/src/solver/`）**: `occurrence.rs`・`partial_eval.rs`・`revision.rs`・`multisource.rs`（必要に応じて機能単位で分割）。
  - **変換層（`crates/shigure/src/convert/`）**・**入力層（`crates/input/src/law/shigure/`）**・**CLI 接続（`src/run/shigure/`）**: 既存 Phase 1〜4 の変換・静的検査・出力形式（`archsig.summary/1`・`archsig.result/4`）へ一貫して統合する。

### 2. 入力層の後方互換拡張と保護

- `archsig.law/2`（`semantics "archsig/0.6.0"`）の文脈キーワード `shigure` 配下に、4 種別の宣言（`occurrence`・`partial`・`revision`・`multisource`）を追加する。予約語を増やさず、既存 Lexer を変更しない。
- 各宣言は `origin`（`ArchMap` origin 参照または明示 `OriginKind`＋ソース参照）を必須とし、参照した由来のみを結果の provenance へ継承する。
- **結論注入の拒否**: 機能閉包結果・衝突導出列・文脈同値分割・分離文脈・最小属性値域・極小不整合部分提示・超評価結果・無効化錐・SNF 分解結果・極小衝突集合・最小由来支持などに相当する結論フィールド名・識別子を宣言・句・変数位置に書いた場合は構文／検査エラー（exit 65）で拒否する。
- **必須 Law の補完非混入（例 18.2）**: 部分提示において、背景構造制約と評価対象 Law を構文・IR の両方で分離し、評価対象 Law を補完条件へ混入しない。

### 3. 4 種別の計算核と対応する数学本文

#### 3.1 `shigure_occurrence`（第17章：出現の同定と観測語彙）

- **最小機能閉包と記録衝突（定理 17.2・命題 17.3）**: 複数 sort の有限出現集合 $E_s$、同一視要求 $\mathscr{R}_s$、固定値 sort（相異なる固定値は同一視不可）、正負の出力記録（$G_e^+, G_e^-$）・定義域記録（$D_p^+, D_p^-$）・関係記録（$r^+, r^-$）から最小機能閉包 $\theta^{\min}(\mathcal{E})$ を構成する。固定値衝突または正負記録衝突がある場合は `refuted` とし、要求・同値律・機能性適用をたどる**有限導出列**を返す。
- **使用文脈同値と健全な商（定義 17.4・設定 17.5・定理 17.6・例 17.7・命題 17.8）**: 基本読取りと操作代入から反復細分で文脈同値 $\approx_{\mathcal{V}}$ と各区別の**分離文脈**を構成する。設定 17.5 の文脈閉性を満たす場合は最粗の健全な同定を返し、部分記録や部分グラフ不在を含む一般の有限系では健全な同定の全体・存在有無・最粗商の有無を判定する（例 17.7 の最粗商不存在を正確に区別する）。
- **補助属性の最小値域と別名／変換／解釈（設定 17.9・定理 17.10・定理 17.11・例 17.12・例 17.13）**: 初期読み出し $p_s$ に対し、(a) 評価分離のみの最小値域濃度 $\kappa_s$、(b) 操作保存・初期読み出し保持を含む健全同定の極小値域組 $(\kappa_s(\theta))_s$ と具体的属性割当て、または不存在根拠を分離して計算する。例 17.12（評価分離 2 値 vs 操作保存 3 値、同一視要求追加による最小機能閉包衝突）および例 17.13（別名受渡し・変換前後・多解釈タグ）を独立フィクスチャで再現する。

#### 3.2 `shigure_partial`（第18章：部分提示・欠測と開領域の確定評価）

- **部分提示の整合性と極小不整合抽出（定義 18.1・例 18.2・定理 18.3）**: 既知値・明示不在・名前付き未観測スロット $\Xi$（複数項目での共有を含む）を区別し、有限表表示または体（$\mathbb{Q}$ / $\mathbb{F}_p$）・整数環（$\mathbb{Z}$）上のアフィン表示（$x = x_0 + T t, C x = d$）の補完ファイバー $\operatorname{Comp}(P)$ の非空性を判定する。$\operatorname{Comp}(P) = \varnothing$ の場合は「不整合」として記録し、**包含極小な不整合部分提示（MUS）**を根拠つきで抽出する。
- **強 Kleene 三値評価・超評価・アフィン正規化（定義 18.4・構成 18.5・定理 18.6・例 18.7・定理 18.8・命題 18.9）**:
  - 構成 18.5 の強 Kleene 三値評価（正格な `let` 束縛、未定義項を引数に持つ原子式の $\mathsf{F}$ を含む）と、全補完上の超評価 $\operatorname{Val}_P(\varphi)$、およびアフィン正規化による確定評価（$Bx_* = e \wedge BK = 0$ / 不能 / 未決）を分離して出力する。
  - 条件付き Law $\ell = (\iota \vdash \chi)$ について、前件の適用区分（適用確定・不適用確定・適用混在）と適用補完上の結論評価を分けて保持する。
  - 例 18.7 の 3 種相関（$\xi - \xi = 0$、$\exists x (x = \xi)$、全域操作の $G_f(*, 0) \vee G_f(*, 1)$）で強 Kleene の `?` と超評価／アフィン正規化の $\mathsf{T}$ の差を検証する。
- **解の量化 4 階層と必要スロット（定義 18.10・命題 18.11・定理 18.12）**: 共通候補集合 $C$ と有効性関係 $\mathrm{Valid}(A, c)$ に対し、$E$・$U$・$G$・$Q$ の 4 階層をすべて独立に判定し（$G \iff U \wedge Q$、$U$ と $Q$ の比較不能）、確定出力 $p: \mathcal{A} \to Z$ に必要なスロット集合の全包含極小十分集合（極小横断集合）または不能 witness（空の不一致集合 $E_{A, A'} = \varnothing$）を返す。
- **開領域の局所網羅と制限修復（定義 18.13・命題 18.14・例 18.15・定理 18.16・命題 18.17・定理 18.18）**: 充満部分構造埋め込み $A_0 \hookrightarrow A$ と参照操作ファイバーの局所網羅条件 $p_A^{-1}(B) \subseteq X_s(A_0)$ を検査し、正の存在式・量化なし反例の保存、外部存在量化による反例解消（例 18.15）、および局所網羅範囲での Law 評価一致を判定する。さらにアフィン制限 $r$ の像 $Rp_* + R(\ker M)$ とファイバー方向 $\ker M \cap \ker R$ による大域一意修復の検査（定理 18.18）に対応する。

#### 3.3 `shigure_revision`（第19章前半 19.1–19.3：改訂・無効化錐・SNF 再利用）

- **追記と改訂スパン（定義 19.1・命題 19.2）**: 追記 $P_1 \hookrightarrow P_2$ と改訂スパン $P_1 \hookleftarrow P_0 \hookrightarrow P_2$ を区別する。追記後の補完が非空なら確定評価と条件付き Law 適用区分が単調保存されることを検証し、追記後に補完が空になる場合は不整合として保存主張を適用しない。
- **構造制約から作る意味的無効化錐（設定 19.3・定理 19.4・例 19.5）**: 原始座標 $\Lambda$ と構造制約（一価性・全域性・定義域・共有スロット・参照先選択候補）の支持 $S_c \subseteq \Lambda$ から、変更集合 $\Delta$ の最小閉包 $C = \operatorname{Cone}(\Delta)$ を計算する。両端補完の非空性を独立検査した上で、錐外座標 $W \subseteq \Lambda \setminus C$ への射影像一致 $\operatorname{pr}_W \operatorname{Comp}(P_1) = \operatorname{pr}_W \operatorname{Comp}(P_2)$ と錐外評価不変性を検証する。例 19.5（固定制約 $\xi = \eta$ による構文外の波及、および不整合追記時の非適用）を検証する。
- **作用素と右辺を分離した修復計算（補題 19.6・定理 19.7）**: 体 $\mathbb{Q}$ および整数環 $\mathbb{Z}$ 上の修復系 $Mp = b$ について、SNF $UMV = D$（単因子 $d_1 \mid \cdots \mid d_r$・可逆行列 $U, V$・$\ker M$・$\operatorname{coker} M$）を計算し、$UMV = D$ を検算する。作用素を決める部分提示 $P_{\mathrm{op}} \subseteq P_0$ が共通部分に残り、改訂が右辺 $P_{\mathrm{rhs}}$ または由来ラベルのみである条件を検査した上で、新右辺 $b^{(2)}$ の整除条件 $d_i \mid u_i$（$i \le r$）・零行条件 $u_i = 0$（$i > r$）から全解ファイバー $p = V y$ を復元し元方程式へ再評価検算する。作用素改訂時または共通部分から作用素が一意に定まらない場合は、既存分解の流用を拒否して再計算または理由付き `undetermined` を返す。

#### 3.4 `shigure_multisource`（第19章後半 19.4–19.5：多源高次衝突と最小由来支持）

- **多源提示と高次の構造衝突（定義 19.8・定理 19.9）**: 有限添字集合 $\mathcal{I}$ の各観測源 $P_\alpha$（各源の由来 `OriginKind`・ソース参照を保持）を上書きせず合併 $P_J$ して整合性を検査し、$\operatorname{Comp}(P_J) = \varnothing$ となる**すべての包含極小衝突源集合 $J \subseteq \mathcal{I}$** を有限列挙する。任意の 2 源合併が整合しても 3 源以上で破綻する高次構造衝突（定理 19.9 の全域操作 3 値禁止例など）を確実に検出する。
- **検証後に結論を支える最小由来支持（設定 19.10・定理 19.11・命題 19.12・例 19.13）**: 信頼済み提示 $T$・有限個の未確認候補 $(h_i)_{i \in I}$（任意に非負整数／非負有理数費用 $c_i$ を指定）・目標結論 $(\varphi, v)$ に対し、悪い補完族 $\mathcal{B}_v$ と不一致集合 $E_A$ から**すべての包含極小由来支持 $S \subseteq I$** および費用指定時の**費用最小の包含極小支持**を計算する。
  - 候補全体が整合しない場合は、横断条件に加えて $\operatorname{Comp}(T_S) \ne \varnothing$ を個別に検査し、空補完を支持として採用しない。
  - 全候補を検証しても不足する場合（ある $A \in \mathcal{B}_v$ で $E_A = \varnothing$）は `refuted` とし、その悪い補完 $A$ を不足 witness として返す。
  - 最小支持 $S$ 採用後に残余候補 $I \setminus S$ を撤回または反転しても結論 $v$ が維持されること（定理 19.11 の安定性）を検算する。また、検証結果が候補 $h_i$ と異なった場合に、その候補を採用せず改訂スパンとして再計算する経路を確認する。例 19.13（$\omega = \xi - \eta$ における二通りの最小支持 $\{\omega = 0\}$ と $\{\xi = 0, \eta = 0\}$）を検証する。

### 4. 判断不能（`undetermined`）と適用境界の規律

次の条件外入力では誤った `established` / `refuted` や暗黙の近似を返さず、明示的な理由コードを添えた `undetermined`（CLI `status: "partial"`, exit 2）を返す。

- 有限列挙上限超過（出現数・同値関係候補数・補完数・スロット数・源数・未確認候補数・部分集合探索ステップの上限超過）
- 有限表でもアフィン表示（$\mathbb{Q}$ / $\mathbb{F}_p$ / $\mathbb{Z}$）でもない非対応補完クラス（例: 非線形制約・非対応係数環・無限担体量化）
- 作用素が共通部分から一意に定まらない、または作用素改訂時に分解再利用を強制指定された場合
- 入力の `observed Entity.field` 参照先が欠測であり、部分提示スロットとして明示宣言されていない未観測依存

## Acceptance Criteria

| AC | 種別 | 確認する成果 |
| --- | --- | --- |
| AC1 | 実装検証系 | **先行分割・モジュール境界・IR 固定**: `crates/computation/src/observed/` および `crates/input/src/law/lexer.rs` への変更が 0 件である。900 行超の追記対象既存ファイルは機能追加前に責務分割され、新規・実質変更対象の全 Rust ファイルが 1,000 行未満に収まっている。`crates/shigure/src/{algebra,ir,convert,solver}/`・`crates/input/src/law/shigure/`・`src/run/shigure/` が責務分離されている。 |
| AC2 | 実装検証系 | **入力層後方互換拡張と保護**: `archsig.law/2`（`semantics "archsig/0.6.0"`）の `shigure` 配下へ `occurrence`・`partial`・`revision`・`multisource` 宣言を追加し、型・参照・由来（`OriginKind` 4 種）・背景制約と評価 Law の分離を検査できる。結論注入・不正参照・由来欠落は exit 65 で拒否され、既存全テスト・既存フィクスチャ（通常経路および Phase 1〜4 SHIGURE 経路）が一切退行せず通過する。 |
| AC3 | 実装検証系 | **第17章 出現同定と観測語彙（`shigure_occurrence`）**: 独立フィクスチャと E2E・計算核テストで次をすべて確認する。(a) 最小機能閉包と固定値／正負記録衝突の有限導出列（定理 17.2・命題 17.3）。(b) 反復細分による文脈同値・分離文脈・最粗健全商（定理 17.6・命題 17.8）および部分記録・部分グラフ不在での最粗商不存在（例 17.7）。(c) 評価分離と操作保存それぞれの最小補助属性値域と属性構成（例 17.12 の 2 値 vs 3 値、要求追加による衝突、例 17.13 の別名・変換・多解釈タグ）。 |
| AC4 | 実装検証系 | **第18章 部分提示・欠測と開領域（`shigure_partial`）**: 独立フィクスチャと E2E・計算核テストで次をすべて確認する。(a) 明示不在と未観測の分離、有限表・アフィン表示の整合性判定、不整合時の包含極小不整合部分提示（MUS）抽出、必須 Law の補完非混入（例 18.2・定理 18.3）。(b) 強 Kleene 三値評価（正格 `let` 含む）と超評価／アフィン正規化の比較、条件付き Law の適用区分、例 18.7 の 3 種相関。(c) 解の量化 4 階層 $E/U/G/Q$ の分離（命題 18.11）と必要スロットの極小横断集合・不足 witness（定理 18.12）。(d) 開領域の局所網羅検査・正の存在式保存・外部存在量化による反例解消（例 18.15・定理 18.16）およびアフィン制限の一意修復判定（定理 18.18）。 |
| AC5 | 実装検証系 | **第19章前半 改訂・無効化錐・SNF 再利用（`shigure_revision`）**: 独立フィクスチャと E2E・計算核テストで次をすべて確認する。(a) 非空追記での確定評価・適用区分単調保存と空補完不整合時の非適用（定義 19.1・命題 19.2）。(b) 構造制約支持からの $\operatorname{Cone}(\Delta)$ 計算・両端非空検査・錐外射影像と評価の不変性・例 19.5 の構文外依存と不整合追記。(c) $\mathbb{Q}$ / $\mathbb{Z}$ の SNF $UMV = D$ 検算と作用素不変時の右辺／由来改訂に対する全解復元・元方程式再評価一致（定理 19.7、例 $2p = b$ の $b=2,4,3$ 対比含む）、および作用素改訂時の再利用拒否。 |
| AC6 | 実装検証系 | **第19章後半 多源衝突と最小由来支持（`shigure_multisource`）**: 独立フィクスチャと E2E・計算核テストで次をすべて確認する。(a) 2 源ペアワイズ整合かつ 3 源以上で破綻する高次構造衝突を含む全包含極小衝突集合の列挙（定理 19.9）。(b) 信頼済み提示＋未確認候補に対する全包含極小由来支持・費用最小化（例 19.13 の二通り最小支持）、非整合候補族での個別非空性検査（空補完非採用）、不足時の悪い補完 witness、最小支持採用後の残余撤回／反転に対する結論安定性検算、および検証不一致時の改訂スパン再評価（定理 19.11・命題 19.12）。 |
| AC7 | 実装検証系 | **判断不能規律と代数的性質の網羅検証**: 機能閉包の最小性、強 Kleene の超評価に対する健全性、$G \iff U \wedge Q$、追記単調性、$\operatorname{Cone}(\Delta)$ 錐外射影一致、SNF 恒等式 $UMV = D$、最小由来支持の包含極小性・安定性、および上限超過・非対応補完クラス・未宣言未観測依存での理由付き `undetermined`（`status: "partial"`, exit 2）を単体・パラメトリック・E2E テストで確認する。 |
| AC8 | 実装検証系 | **恒久仕様書同期と品質確認**: 導入した DSL 宣言・標準構成・CLI 4 問い・出力スキーマ・適合例を `docs/tool/archsig_v0_6_0_io/`（`law.md`・`computations.md`・`execution.md`・`results.md`・`validation.md`）および `tools/archsig_v0.6.0/README.md` へ同期反映する。`cargo fmt --check`・関連 Clippy lint（`-D warnings`）・`cargo test --workspace`・`cargo test --doc`・`git diff --check`・不可視／双方向制御 Unicode 検査・語彙ルール検査をすべて通過する。 |
| AC9 | 実装検証系 | **代表規模ベンチマーク実測**: 数百対象・数千 Atom 級の固定代表入力（既存ベンチ入力および Phase 5 の 4 問いを含む固定代表入力）について、release ビルドで変更前後の実行時間と最大 RSS を実測比較し、既存経路の著しい退行がなく、新規 4 問いの計算費用が一次実測値として Issue / PR へ記録されている。 |

## 失敗判定条件（Failure Contract）

次のいずれかに該当する場合は未達（失敗）とする。

1. `crates/computation/src/observed/` または `crates/input/src/law/lexer.rs` へ変更を加えた、あるいは 1,000 行超の肥大化ファイルを分割せずに機能追記した。
2. 結論注入（閉包結果・分割・MUS・無効化錐・SNF・極小衝突・最小由来支持等の外部入力）が入力検査をすり抜ける、または必須評価 Law を補完条件へ混入して不適合と入力不整合を混同した。
3. 明示不在と未観測、評価分離と操作保存の最小属性値域、$E / U / G / Q$ の 4 階層、追記と改訂スパン、ペアワイズ整合と高次多源整合、または候補の採用前後を混同した。
4. 適用条件外・計算上限超過・空補完のケースで、理由付き `undetermined` や明示的不整合ではなく誤った `established` / `refuted` を返した。
5. 復元した属性割当て・補完・SNF 解ファイバー・最小由来支持の安定性に対して独立した再評価検算を欠いた。
6. 既存テスト・既存 SHIGURE Phase 1〜4 フィクスチャの退行、恒久仕様書との乖離、または代表規模ベンチマーク実測の欠落がある。

## 実装計画（依存順のステップ）

実際の Issue / PR の分割・統合単位は実装ループ側で到達点とレビュー可能性から判断する。依存順の標準ステップは次の通りとする。

1. **Step 1（先行分割・基盤アルゴリズム・IR 固定）**: 追記対象となる 900 行超ファイルの先行分割を行い、`crates/shigure/src/algebra/` に導出列付き機能閉包・反復細分・最小横断集合・整数 SNF（$UMV = D$）を、`crates/shigure/src/ir/` に Phase 5 検証済み IR と `result_phase5` 型を固定する。
2. **Step 2（計算核 Part A: 第17章・第18章）**: `shigure_occurrence` と `shigure_partial` の計算核および単体・パラメトリックテスト（例 17.7・17.12・17.13・18.2・18.7・18.15 を含む）を実装する。
3. **Step 3（計算核 Part B: 第19章）**: `shigure_revision` と `shigure_multisource` の計算核および単体・パラメトリックテスト（例 19.5・定理 19.7・定理 19.9・例 19.13 を含む）を実装する。
4. **Step 4（入力層・変換層・結論注入保護）**: `crates/input/src/law/shigure/` へ 4 宣言の AST・パーサ・静的検査（結論注入拒否・由来保護・背景/Law 分離）を、`crates/shigure/src/convert/` へ変換層を追加する。
5. **Step 5（CLI 接続・独立 E2E 検証）**: `src/run/shigure/` へ 4 問いを接続し、独立 Phase 5 フィクスチャ群による実バイナリ E2E テスト（正常・反証・判断不能・結論注入 exit 65・複数 SHIGURE 問い同時実行・`--out` 保存）を検証する。
6. **Step 6（恒久仕様書同期・代表規模ベンチマーク・最終完了レビュー）**: 恒久 I/O 仕様 5 文書と `tools/archsig_v0.6.0/README.md` を同期し、代表規模 release ベンチマークを実測記録する。独立 2 lane の `$prd-completion-review` で達成判定を得た後、本 PRD を削除整理する。

## 対象外（Non-goals）

- 同梱 SKILL（`tools/archsig_v0.6.0/skills/`）の SHIGURE 統合、代表 OSS 通し実測 QA、キャッシュ（`--reuse` の SHIGURE 再利用最適化）・予算制御、外部解析ツール接続（いずれも Phase 6 の対象）。
- AAT 第VI部 第20章・第21章の新規構成（20.5 の自然な極大安全粗視化、20.9–20.11 の最小公開補完、21.6 の構造パラメータ層別化、21.10 の適応的観測決定木、21.11–21.14 の整数剰余観測・上書き置換と許可範囲×観測費用の同時最適化）および第VII部・付録E（Phase 6 実測後の拡張候補）。
- 数学本文（`docs/aat/algebraic_geometric_theory/`）・Lean 形式化（`Formal/`・`research/lean/`）・ArchView・FieldSig・website・CI ワークフローの変更。
- 非線形な部分提示補完の一般求解や、無限担体上の量化・無限制約に対する一般決定手続き。

## 停止条件

- 既存 `archsig.law/2` の後方互換性を破らずに 4 宣言のいずれかを表現できない構文衝突が見つかった場合は、入力仕様の拡張方針を人間へ戻して判断を仰ぐ。
- 900 行超の既存ファイル分割が Phase 1〜4 の公開 API やテストへ広範な波及を生む場合は、分割範囲を明確化して先にリファクタリング Issue として切り出す。
- 数学本文 第17〜19章の仮定とツール側有限表現のあいだに仕様未定義の境界が見つかった場合は、場当たり的な近似を入れず、設計判断事項として人間へ戻す。
