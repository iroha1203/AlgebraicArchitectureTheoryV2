# SHIGURE Lean 形式化 PRD（第I部・付録A：基盤・Law と意味の基礎）

| 項目 | 内容 |
| --- | --- |
| 状態 | Draft |
| 対象配置 | `Formal/SHIGURE.lean`, `Formal/SHIGURE/**`, `.github/workflows/lean.yml` |
| 親計画 Issue | GitHub Issue `#6439` |
| 数学本文（Tier 1 参照先） | [第1章](../aat/algebraic_geometric_theory/part_1/chapter_1_atoms_laws_theories.md), [第2章](../aat/algebraic_geometric_theory/part_1/chapter_2_models_and_morphisms.md), [第3章](../aat/algebraic_geometric_theory/part_1/chapter_3_contexts_and_local_models.md), [付録A](../aat/algebraic_geometric_theory/appendix_a_positive_logic.md), [共通記号](../aat/algebraic_geometric_theory/notation.md) |
| 適用ガイドライン | [AAT guideline](../aat/guideline.md), [Lean 品質基準](../aat/lean_quality_standard.md), [Workflow guideline](../workflow/guideline.md), [PRD guideline](guideline.md), [語彙ルール](../workflow/vocabulary.md) |
| CI 変更承認 | 人間により `.github/workflows/lean.yml` への `Formal/SHIGURE` 専用ジョブ追加が承認済み |

---

## 1. 問い

> 既存の `Formal/AG/`、`Formal/Util/`、`research/lean/ResearchLean/` を一切再利用せず、`Formal/SHIGURE/` 配下に独立した Lean 4 基盤・標準公理監査・CI を構築したうえで、数学本文の第I部（第1–3章）と付録Aのすべての定義・構成・証明付き主張（17 件）・具体例（7 件）を、仮定の追加や結論の弱化なしに Lean カーネルで検証できるか。

---

## 2. 現状診断

- 数学本文 `docs/aat/algebraic_geometric_theory/`（全 6 部 19 章 + 付録 A–F）は完成しており、第I部（第1–3章）と付録Aは「証明はこの部と付録Aの中で閉じる」自己完結した基礎層である。
- リポジトリの Lean 環境は `leanprover/lean4:v4.28.0` / `mathlib v4.28.0`、`lakefile.toml` は `[[lean_lib]] name = "Formal"` である。
- 現行の `Formal/` 配下には `Formal/AG/` と `Formal/Util/` が存在するが、`Formal/SHIGURE/` および `Formal/SHIGURE.lean` は未作成である。
- 現行の `.github/workflows/lean.yml` は `Formal/AG/` 変更時のみ `lake build +Formal.AG` と `Formal/AG/AxiomAudit.lean` を実行しており、`Formal/SHIGURE/` のビルド・公理監査・孤立 import 検査は未整備である。

---

## 3. 全体設計と不変条件

### 3.1 完全独立の不変条件（既存成果の非再利用）

- `Formal/SHIGURE/**` および `Formal/SHIGURE.lean` が import できるのは `Mathlib.*`、`Std.*`、`Lean.*`、`Formal.SHIGURE.*` のみに限定する。
- 次の一致が **0 件** であることをローカルおよび CI の機械検査で保証する：
  - `import Formal.AG`（配下モジュール含む）
  - `import Formal.Util`（配下モジュール含む）
  - `import ResearchLean`（配下モジュール含む）
- 標準公理監査コマンドは `Formal/SHIGURE/AssertStandardAxioms.lean` として独立に実装し、その自己テスト（`Formal/SHIGURE/AssertStandardAxiomsTest.lean`）および全主定理監査エントリポイント（`Formal/SHIGURE/AxiomAudit.lean`）を `Formal/SHIGURE/` 配下に置く。
- `Formal.lean` および `Formal/AG/` は変更しない。`lakefile.toml` は現行の `[[lean_lib]] name = "Formal"` を維持し、`lake build +Formal.SHIGURE` で独立ビルドする。

### 3.2 数学本文との整合・Lean 品質規律

- すべての新規宣言は [Lean 品質基準](../aat/lean_quality_standard.md) に従う：
  - **§1.1 material premise の三分類申告**：PR 本文で各定理の仮定を「本文由来（部・定理番号つき）」「放電済み（放電宣言名つき）」「未放電」に分類して申告する。未放電仮定を持つ定理は本 PRD の完了根拠としない。
  - **§1.2 premise 使用性**：未使用引数を残さない。
  - **§1.3 API 接続義務**：圏（$\mathbf{Th}, \mathrm{Str}_\Sigma, \mathcal A_{\mathbb T}, \mathcal A_{\mathrm{tot}}, \mathbf{Lens}, \mathbf{Prot}(\mathcal E,O), \mathrm{Ctx}(\mathcal P), \mathrm{Match}$）、関手・自然同型・圏同値、環・加群・多項式環・商環・局所化は mathlib（`CategoryTheory`, `Algebra`, `MvPolynomial`, `Ideal.Quotient`, `Localization` 等）へ直接接続する。
  - **§1.4 instance ペア**：新規の `Prop` 述語や構造に対し、肯定・否定の双方の witness を備える（本文の例 1.6, 1.10, 2.7, 2.13, 3.7, 3.10, 3.12 および本文中の反例を直接形式化する）。
  - **§2.1–2.5**：小さい定義、data と `Prop` の分離、definitional escape 禁止、mathlib 再発明禁止、no-unfold API（`ext` / constructor / destructor / 特徴づけ補題を定義と一体で提供）、自明でない表現選択への `Implementation notes` 記載。
  - **§4.1 標準公理検査**：許容するカーネル公理は `propext`, `Classical.choice`, `Quot.sound` のみ。`axiom`, `admit`, `sorry`, `unsafe`, `native_decide`（`Lean.ofReduceBool`）を禁止する。
- **集合論・宇宙・空担体の規約**（[共通記号](../aat/algebraic_geometric_theory/notation.md)・[付録A](../aat/algebraic_geometric_theory/appendix_a_positive_logic.md) A.1）：
  - 各担体、宣言族、Law 族は固定した小さい宇宙 `Type u`（または具体構成では `Type`）で扱い、空の担体を許す。したがって、導出体系には「未使用変数を文脈から無条件に除去する規則」を入れない。
  - 変数文脈 $\Gamma = (x_1:s_1,\dots,x_n:s_n)$ の構文表現（例：型付き de Bruijn index / `List S` 添字による変数・束縛表現で $\alpha$-同値と捕獲回避を内在化）など表現選択は `Implementation notes` に明記し、数学本文の構文・評価・代入・翻訳と同値であることを損なわない設計にする。
- **Lean build 運用（hard rule）**：[AAT guideline](../aat/guideline.md) に従い、ローカル確認は単一ファイル `lake env lean <target-file>` および必要時の対象モジュール `lake build <module>` とし、フル `lake build` は CI（`lake build +Formal.SHIGURE`）で行う。サブエージェントの `lake build` は全面禁止する。

### 3.3 推奨モジュール配置

```text
Formal/
├── SHIGURE.lean
└── SHIGURE/
    ├── AssertStandardAxioms.lean
    ├── AssertStandardAxiomsTest.lean
    ├── AxiomAudit.lean
    └── Part1/
        ├── Signature.lean            -- 定義1.1, 1.2, 式(1.1)-(1.2)
        ├── Syntax.lean               -- 定義1.3, 1.4, 1.5, 1.7, 式(1.3)-(1.8)
        ├── Preservation.lean         -- 定理1.8, 定義1.9, 1.11, 式(1.9)-(1.12)
        ├── PositiveLogic.lean        -- 付録A: A.1, 命題A.1, 命題A.2, 補題A.3, 命題A.4
        ├── Chapter1Examples.lean     -- 例1.6, 例1.10
        ├── Models.lean               -- 定義2.1, 2.2, 命題2.3, 式(2.1)-(2.3)
        ├── Pullback.lean             -- 定理2.4, 系2.4a, 構成2.5, 式(2.4)-(2.7)
        ├── OperationWords.lean       -- 定理2.6, 例2.7, 式(2.8)-(2.9)
        ├── Lens.lean                 -- 定義2.8, 定理2.9, 命題2.10, 式(2.10)-(2.13)
        ├── Protocol.lean             -- 定義2.11, 定理2.12, 例2.13, 式(2.14)-(2.15)
        ├── Contexts.lean             -- 定義3.1, 命題3.2, 定義3.3, 定理3.4, 定理3.5, 式(3.1)-(3.3)
        ├── MarkedModules.lean        -- 命題3.6, 例3.7, 式(3.4)-(3.5)
        └── FragmentsAndRings.lean    -- 定義3.8, 例3.10, 命題3.11, 例3.12, 式(3.7)-(3.9)
```

（1 ファイルが過大になる場合は `Part1/<Topic>/` 配下へ細分化してよいが、`Formal/SHIGURE.lean` から到達可能であること。）

---

## 4. 一次仕様（Target Statements）と受け入れ条件（Acceptance Criteria）

本節を本 PRD における **target statement の一次仕様**（[Lean 品質基準](../aat/lean_quality_standard.md) §5）とする。各 AC の数学的主張・仮定・結論の正典は対応する数学本文の番号付き項目であり、仮定の追加・結論の弱化・対象縮小（有限化・固定化等）を禁止する。

### AC-01: 独立基盤・公理監査コマンド・孤立 import 検査・CI ジョブ

- `Formal/SHIGURE.lean` を新設し、namespace `SHIGURE`（配下サブ namespace 含む）の集約ルートとする。
- `Formal/SHIGURE/AssertStandardAxioms.lean` を独立に実装し、指定 namespace 配下のモジュール内宣言が `propext`、`Classical.choice`、`Quot.sound` のみに依存することを検査するコマンド `#shigure_assert_standard_axioms_only <ns>`（空対象をエラーとし、`sorryAx` / カスタム `axiom` / `Lean.ofReduceBool` を拒否する）を提供する。
- `Formal/SHIGURE/AssertStandardAxiomsTest.lean` により、正常パス（標準公理のみ）と異常パス（カスタム `axiom` / 空 namespace の拒否）の双方を検証する。
- `Formal/SHIGURE/AxiomAudit.lean` を作成し、最終非空行に `#shigure_assert_standard_axioms_only SHIGURE.AxiomAudit` を置く。
- `.github/workflows/lean.yml` に `Formal/SHIGURE` 専用ジョブを追加する（対象パス：`Formal/SHIGURE/**`, `Formal/SHIGURE.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `.github/workflows/lean.yml`）。ジョブは以下を実行する：
  1. 孤立 import 検査：`Formal/SHIGURE` および `Formal/SHIGURE.lean` 内に `import Formal.AG` / `import Formal.Util` / `import ResearchLean` が 0 件であること。
  2. `lake build +Formal.SHIGURE`
  3. 独立公理監査：`lake env lean Formal/SHIGURE/AssertStandardAxiomsTest.lean`、`lake env lean Formal/SHIGURE/AxiomAudit.lean`、および末尾コマンド行の検証。
  4. `sorry` / `admit` / `axiom` / `unsafe` の 0 件検査（`AssertStandardAxiomsTest.lean` 内の意図的な異常系テスト構文は明示分離する）。

### AC-02: 第1章 1.1–1.3（Atom 語彙・署名・構造・項・正の式・Law・残差）と例 1.6

- **定義 1.1（型付き Atom 語彙）**：7 種類（sort・操作・関係・部分操作・量・Law・式の出現）のタグ付き区別、宣言側集合 $\mathrm{At}_{\mathrm{dec}}(\mathcal P)$、評価事実側集合 $\mathrm{At}_{\mathrm{val}}(A)$（入力タグ保持、部分操作は $D_p^A$ のみ）。
- **定義 1.2（署名とその解釈データ）**：小さい sort 集合 $S$、有限 arity（$n=0$ 含む）の全域操作・関係・部分操作・量（印付き全域操作）、構造 $A$（空担体許容、空積は一元集合）、グラフ関係 $G_f, G_q, G_p$・定義域 $D_p$。式(1.1) のグラフの構造公理が全構造で成立すること、および逆に式(1.1)を満たすグラフ関係から全域写像・部分写像が一意に回復することを証明する。式(1.2) の包含 sort による定義域指定 Law の構成を与える。
- **定義 1.3（項と部分評価）**：変数・操作/量適用・strict 束縛式 $\mathrm{let}\,z=t\,\mathrm{in}\,s$（本体に $z$ が現れなくても $t$ を先に評価）、部分評価 $\mathrm{ev}_A(t,\gamma)$ と定義域 $\mathrm{Dom}_A(t)$、値グラフ式 $E_t(\boldsymbol x,y)$（式(1.3)）と $\mathrm{Def}_t(\boldsymbol x)$。構文帰納法により $A \models E_t(\gamma,b) \iff (\gamma \in \mathrm{Dom}_A(t) \land \mathrm{ev}_A(t,\gamma)=b)$、一価性、および $\mathrm{Def}_t$ の充足領域と $\mathrm{Dom}_A(t)$ の一致を証明する。
- **定義 1.4（正の式）**：基本原子式と $\top,\bot,\wedge,\vee,\exists$、構造での充足、項引数原子式の展開略記（式(1.4)）、および $t=t$ の充足が $\mathrm{Def}_t$ と同値であることの証明。
- **定義 1.5（Law と役割）**：Law $\ell = (\Gamma_\ell, \iota_\ell, \chi_\ell)$、入力集合 $I_\ell^A$・充足 $A \models \ell$（式(1.5)）、理論 $\mathbb T$、3 種の役割（必須・追加・導出）、環値等式 Law の順序対 $(t,t')$・$J_\ell^A$・残差 $\rho_{\ell,A}$（式(1.6)）、および $A \models \ell \iff (J_\ell^A = I_\ell^A \land \forall \gamma \in J_\ell^A,\ \rho_{\ell,A}(\gamma)=0)$ の証明。
- **例 1.6（同じ言語で書かれる Law）**：lens の理論（式(1.7)）と直積モデル $S=V\times C$ の充足証明、有向グラフ経路の理論と往復等式 $g(f(x))=x$、可換環と加群の理論の構成（および非充足の否定モデル例）。

### AC-03: 第1章 1.4–1.5（原始表示・代入・定理 1.8・理論解釈・例 1.10・観測と reading）

- **定義 1.7（原始表示と代入）**：原始表示 $\mathcal P$ と指定理論 $\mathbb T_{\mathcal P}$、代入 $\theta$、$t[\theta]$、$\varphi[\theta]$、$\mathrm{Def}_\theta$、$D_{\theta,A}$、評価写像 $\theta_A$（式(1.8)）、Law 代入 $\ell[\theta]$、環値等式 Law の順序対代入。
- **定理 1.8（代入・評価・構造射による保存）**：(1) $\delta \in D_{\theta,A}$ 上での項の定義可能性・評価の一致および正の式充足の同値、(2) 式(1.9)を満たす写像族 $h_s$ による項の定義域・評価（式(1.10)）・正の式充足・入力集合 $h_{\Gamma_\ell}(I_\ell^A) \subseteq I_\ell^B$ の保存、(3) 環準同型 $h_R$ 下での $h_{\Gamma_\ell}(J_\ell^A)\subseteq J_\ell^B$・残差可換式(1.11)・代入残差 $J_{\ell[\theta]}^A$ と $\rho_{\ell[\theta],A}(\delta)=\rho_{\ell,A}(\theta_A\delta)$。
- **定義 1.9（理論の解釈）**：翻訳データと導出の組 $u:\mathbb T\to\mathbb T'$、式と項の翻訳（strict 束縛式による引数定義可能性の保持）、相互導出による解釈の同値関係、恒等解釈および合成候補。
- **例 1.10（定義域と入力条件を運ぶ必要）**：$S=\{0,1\}, c=1, D_p^A=\{0,1\}, D_p^B=\{0\}$ の具体構造を構成し、(a) 恒等状態写像が $p(c)=c$ を保存しないこと、(b) $B \models (D_p(x)\vdash p(x)=x)$ かつ $B \not\models (\top\vdash p(x)=x)$ であり、健全性により恒等記号翻訳候補が定義 1.9 の解釈にならないことを証明する。
- **定義 1.11（観測と reading の指定）**：状態観測 $o_A:X_s(A)\to O$（直積始域含む）、族の観測 $q:\mathcal U\to B$、reading、および式(1.12) による reading 比較。

### AC-04: 付録A（正の論理の導出規則・健全性・翻訳・理論の圏 $\mathbf{Th}$）

- **A.1（導出規則）**：7 規則（前提と切断・変数置換と未使用変数追加・真偽・連言・選言・存在・等号）を帰納型として定義する（空担体許容のため無条件の変数除去を入れない）。部分項代入 $\theta$ に対する $\exists\boldsymbol x\,(\bigwedge_i E_{\theta_i} \wedge \varphi(\boldsymbol x)) \dashv\vdash \mathrm{Def}_\theta \wedge \varphi[\theta]$ および $\varphi\vdash_\Gamma\psi \implies \mathrm{Def}_\theta\wedge\varphi[\theta]\vdash_\Delta\psi[\theta]$ を導出定理として証明する。
- **命題 A.1（導出の健全性）**：モデル $A$ と導出 $\mathbb T \vdash (\varphi\vdash_\Gamma\psi)$ に対する意味的含意の証明。
- **命題 A.2（導出の翻訳）**：第 1 段（任意の項の値グラフの一価性 $E_t(\boldsymbol x,y)\wedge E_t(\boldsymbol x,z)\vdash y=z$ の構文的導出）、第 2 段（式(1.1)の翻訳導出）、第 3 段（任意導出の翻訳）をすべて証明する。
- **補題 A.3（項と式の翻訳の比較）**：$E_{u(t)} \dashv\vdash u(E_t)$、$\mathrm{Def}_{u(t)} \dashv\vdash u(\mathrm{Def}_t)$、$(v\circ u)(\varphi) \dashv\vdash v(u(\varphi))$、$\mathrm{id}(\varphi) \dashv\vdash \varphi$、および同値解釈 $u \sim u'$ での $u(\varphi)\dashv\vdash u'(\varphi)$・$E_{u(t)}\dashv\vdash E_{u'(t)}$ を証明する。
- **命題 A.4（理論の圏）**：合成候補・恒等候補が定義 1.9 の解釈であること、同値関係が合成と整合すること、単位律・結合律を証明し、mathlib の `CategoryTheory.Category` インスタンスとして理論の圏 $\mathbf{Th}$ を構成する。

### AC-05: 第2章 2.1–2.2（構造の圏・意味圏・固定データ・観測付きモデル・命題 2.3）

- **定義 2.1（構造保存射）**：式(2.1) を満たす構造保存射と、mathlib `CategoryTheory.Category` インスタンスとしての構造の圏 $\mathrm{Str}_\Sigma$（成分外延性補題、同型射と逆写像による関係・定義域保存の特徴づけを含む）。
- **定義 2.2（意味圏）**：意味圏 $\mathcal A_{\mathbb T}$（$\mathrm{Str}_\Sigma$ の充満部分圏）、固定データをもつ意味圏 $\mathcal A_{\mathbb T;M_0}$（部分圏）、観測付きモデルの圏（式(2.2)）と固定構造 $M_0=O$ への埋込み対応。
- **命題 2.3（追加 Law による忘却）**：忘却関手 $\mathcal A_{\mathbb T'} \to \mathcal A_{\mathbb T}$（式(2.3)）の構成と充満忠実性（mathlib `Functor.Full`・`Functor.Faithful`）の証明。加えて本文の冪等 Law $f(f(x))=f(x)$ と 2 点入替操作による本質的全射でない反例を形式化する。

### AC-06: 第2章 2.3（定理 2.4・系 2.4a・構成 2.5）

- **定理 2.4（理論解釈による充足保存と引戻し）**：理論解釈 $u:\mathbb T\to\mathbb T'$ に対する引戻し関手 $u^*:\mathcal A_{\mathbb T'}\to\mathcal A_{\mathbb T}$（式(2.4)）、項の定義可能性・評価一致および正の式充足同値（式(2.5)）、$\mathrm{id}^*=\mathrm{Id}$・$(v\circ u)^*=u^*\circ v^*$（厳密等号または自然同型としての整合を `Implementation notes` に明記）、および同値解釈に対する代表独立性を証明する。
- **系 2.4a（逆解釈からの同値）**：(a) $\mathbf{Th}$ の同型解釈からの逆関手性、(b) 構文的項 $\alpha_s,\beta_s$ とシークエント導出からの自然同型 $\mathrm{Id}\cong u^*v^*$, $\mathrm{Id}\cong v^*u^*$ および圏同値 $\mathcal A_{\mathbb T}\simeq\mathcal A_{\mathbb T'}$（mathlib `CategoryTheory.Equivalence`）を証明する。
- **構成 2.5（理論変更を伴う全体圏）**：全体圏 $\mathcal A_{\mathrm{tot}}$（式(2.6)–(2.7)）の `Category` インスタンス、射影関手 $\pi:\mathcal A_{\mathrm{tot}}\to\mathbf{Th}$、理論 $\mathbb T$ 上のファイバーと $\mathcal A_{\mathbb T}$ の一致、および最大部分 groupoid $\mathcal A_{\mathbb T}^\simeq$（mathlib `CategoryTheory.Core` 接続）を構成する。

### AC-07: 第2章 2.4（定理 2.6・例 2.7）

- **定理 2.6（すべての操作語の保存）**：単項有限操作語 $w$ と定義域 $\mathrm{Dom}_A(w)$、式(2.8)（定義域包含・値可換・観測保存）、定義域反射（式(2.9)）の下での $\mathrm{Dom}_A(w) = h_s^{-1}(\mathrm{Dom}_B(w))$、および理論解釈 $u$ と $h:A\to u^*B$ に対する翻訳版をすべて証明する。
- **例 2.7（非可逆な射と定義域の拡大）**：2 点 $\to$ 1 点の非単射構造保存射、1 点 $\to$ 2 点の非全射構造保存射、および 1 点担体上の $D_p^A=\varnothing, D_p^B=\{*\}$ で式(2.8)が成り立ち式(2.9)が成り立たない具体例を証明する。

### AC-08: 第2章 2.5前半（lens の圏・回復・標準形）

- **定義 2.8（全域 lens の圏）**：全域 lens と式(2.10) の射からなる圏 $\mathbf{Lens}$（mathlib `Category` インスタンス）。
- **定理 2.9（lens の対象とすべての射の回復）**：圏同型 $\mathbf{Lens} \cong \mathcal A_{\mathbb T_{\mathrm{lens}}}$（式(2.11)、対象・射の全単射かつ互いに逆な関手対として構成）および view $V$ 固定版 $\mathbf{Lens}_V \cong \mathcal A_{\mathbb T_{\mathrm{lens}};V}$ を証明する。
- **命題 2.10（基準 view による積表示と射の標準形）**：基準 view $v_0 \in V_L$ に対する全単射 $\theta_L: S_L \simeq V_L \times C_L$（式(2.12)）、この下での `get`/`put` の表示、および射集合の全単射 $\mathrm{Hom}_{\mathbf{Lens}}(L,M) \simeq \mathrm{Map}(V_L,V_M)\times\mathrm{Map}(C_L,C_M)$（式(2.13)）と恒等・合成との整合を証明する。加えて本文の $V=C=\{0,1\}, h(v,c)=(v,v)$ により「読み取り保存だけでは `put` 保存が従わない」反例を証明する。

### AC-09: 第2章 2.5後半（protocol の圏・回復・生成経路・例 2.13）

- **定義 2.11（実行圏上の protocol）**：小さい圏 $\mathcal E$ と $O:\mathcal E\to\mathbf{Set}$ に対する圏 $\mathbf{Prot}(\mathcal E,O)$（`Category` インスタンス）、理論 $\mathbb T_{\mathrm{prot}(\mathcal E)}$（式(2.14)）と固定観測データ $M_0^O$ 下の意味圏 $\mathcal A_{\mathrm{prot}(\mathcal E,O)}$。
- **定理 2.12（protocol の対象・すべての射・生成経路の回復）**：圏同型 $\mathbf{Prot}(\mathcal E,O) \cong \mathcal A_{\mathrm{prot}(\mathcal E,O)}$（式(2.15)）、および有向グラフの経路圏を指定経路等式で割った商圏の場合に生成辺・経路等式 Law・生成辺観測可換性だけから同型に回復できることを証明する。
- **例 2.13（生成辺から合成経路への観測保存）**：3 頂点 $0,1,2$・2 辺 $e,f$、$X(i)=\mathbb Z^2, Y(i)=O(i)=\mathbb Z$、非単射 protocol 射 $h_i(a,b)=a$ を構成し、全経路（空・$e$・$f$・$fe$）での可換性と観測保存を証明する。

### AC-10: 第3章 3.1–3.3前半（宣言文脈・制限・被覆・厳密組立て）

- **定義 3.1（宣言文脈）**：宣言集合 $\mathrm{Decl}(\mathcal P)$、4 種の依存関係（導出 Law が導出木内の全シークエント・文脈・グラフ構造公理・必須 Law に依存することを含む）、宣言文脈 $U$、支持 $\mathrm{Supp}(t),\mathrm{Supp}(\varphi),\mathrm{Supp}(\ell)$、包含の圏 $\mathrm{Ctx}(\mathcal P)$、交差・任意合併での閉性、および制限表示 $\mathcal P|_U$（導出木の有効性保持を含む）。
- **命題 3.2（制限と評価）**：支持が $V$ に含まれる項・正の式・Law の定義域・評価・充足の一致、反変制限関手 $\mathrm{res}_{U,V}:\mathcal A(U)\to\mathcal A(V)$（式(3.1)）、および恒等・合成との厳密整合を証明する。
- **定義 3.3（宣言被覆と厳密な整合族）**：宣言被覆 $(U_i \subseteq U)_{i\in I}$（恒等・引戻し・合成の被覆性）、厳密整合族（式(3.2)）、整合局所射、および圏 $\mathrm{Match}((U_i),\mathcal A)$（`Category` インスタンス）。
- **定理 3.4（宣言被覆上の厳密な組立て）**：厳密整合局所モデル族 $(A_i)$ からの大域モデル $A \in \mathcal A(U)$ の一意存在を証明する。
- **定理 3.5（構造保存射の局所組立て）**：整合局所射からの大域射の一意構成・制限/恒等/合成との可換性、および圏同型 $\mathcal A(U) \cong \mathrm{Match}((U_i),\mathcal A)$（式(3.3)）を証明する。加えて本文の 2 点担体上の操作 $f,g$ と Law $g(f(x))=x$ により「操作のみ覆い Law 宣言を覆わない族では組立てが失敗する」反例を証明する。

### AC-11: 第3章 3.3後半（生成元付き有限局所自由実現の宣言方向組立て・例 3.7）

- **命題 3.6（有限局所自由実現の宣言方向の組立て）**：可換環 $R$ と各型 $s$ の $(m_s, n_s)$ を固定し、式(3.4)（$K_s \subseteq R^{m_s}, Q_s = R^{m_s}/K_s, \pi_s:R^{m_s}\twoheadrightarrow Q_s$、有限局所自由性・階数 $n_s$ — mathlib の `Module.Finite` / `Module.Projective` / 局所自由・階数概念と接続）による生成元付き実現を定義し、交差上で $K_s$ と共有多重線形演算が一致する局所実現族からの一意な大域組立てを証明する。
- **例 3.7（共有の核が一致する場合と異なる場合）**：$R=\mathbb Q$、3 型 $p,q,r$、式(3.5) の $K_q=\mathbb Q(3,-2)$ における成功例（全 Law 充足と組立て）および右側を $K'_q=\mathbb Q(0,1)$ に変更した場合に名前付き生成元を保つ同型 $F:Q_q\to Q'_q$ が存在しないことの証明。

### AC-12: 第3章 3.4–3.5（有限断片・例 3.10・命題 3.11・例 3.12）と最終統合監査

- **定義 3.8（二種類の有限制限）**：宣言の有限断片 $F$ と制限表示 $\mathcal P|_F$（および有限依存閉包条件の下での定理 3.4・3.5 の適用）、ならびに値の有限断片のスキーマと制限写像。
- **例 3.10（有限の答えから全域性が失われる）**：(a) 担体 $\mathbb N$・格子 $Q_n=\{0,\dots,n\}^2$・式(3.7) の $f_n$ により各有限表 $F_n$ は全域写像で実現可能かつ厳密整合だが同時実現する全域写像 $f:\mathbb N\to\mathbb N$ が存在しないこと、(b) $\mathbb N$ 上の有限台 $0,1$ 列の制限族で全成分 $1$ の有限列族が厳密整合だが極限が有限台を持たないこと、の双方を証明する。
- **命題 3.11（宣言忘却に対応する座標環の向き）**：多項式環 $k[Z]$（mathlib `MvPolynomial`）と Law イデアルの商環 $B_V, B_W$ について、誘導される $k$-代数準同型 $B_V \to B_W$ と前合成写像 $\mathrm{Hom}_{k\text{-alg}}(B_W,R) \to \mathrm{Hom}_{k\text{-alg}}(B_V,R)$（式(3.8)）がモデルの忘却と一致することを証明する。
- **例 3.12（共有変数を保つ逆向きの環射がない）**：$B_V = \mathbb Q[x] \to B_W = \mathbb Q[x,y]/(xy-1)$（式(3.9)）について、(a) $x$ を保つ逆向き $\mathbb Q$-代数射が存在しないこと、(b) $B_W \simeq_{\mathbb Q\text{-alg}} \mathbb Q[x, x^{-1}]$（mathlib `Localization.Away`）の同型、の双方を証明する。
- **最終統合監査**：AC-02〜AC-12 の全主定理・命題・補題・系・具体例定理を `Formal/SHIGURE/AxiomAudit.lean` に登録し、CI 上で `lake build +Formal.SHIGURE`、公理監査（標準公理のみ）、孤立 import 検査（0 件）、`sorry`/`admit`/`axiom`/`unsafe` 0 件がすべて合格していること。

---

## 5. Failure Contract（失敗判定条件）

次のいずれかに該当した場合、本 PRD は**未達（Reject）**とする。

1. `Formal/SHIGURE/` または `Formal/SHIGURE.lean` が `Formal.AG`・`Formal.Util`・`ResearchLean` のいずれかを import している。
2. `Formal/SHIGURE/` 配下に `sorry`・`admit`・`axiom`・`unsafe`・`native_decide`（異常系テスト専用の分離箇所を除く）が残存している、または `#shigure_assert_standard_axioms_only` が通らない。
3. 数学本文（第1–3章・付録A）の 17 件の証明付き主張または 7 件の具体例のいずれかに未証明・省略・仮定追加（未放電仮定）・結論弱化・対象縮小（有限化・固定化等）がある。
4. 定義側に結論を埋め込む definitional escape、または mathlib の圏・関手・環・多項式環・商環・局所化と接続しない閉じたラッパーで済ませている。
5. 空の担体を排除する非本文由来の仮定（例：`Nonempty` の無断追加）や、導出規則における無条件の変数除去が混入している。
6. PRD 完了前に、本 PRD への参照がリポジトリ内の他文書・コードに残っている、または恒久規律の更新漏れがある。

---

## 6. 対象外（Non-Goals）

- **問題 3.9（値の有限断片による完全な記述）**：数学本文で将来の課題として明記されており、第IV部・第VI部で扱う範囲のため本 PRD の対象外とする（ただし定義 3.8 と例 3.10 は対象に含める）。
- 第II部以降（第4–19章、付録 B–F）の形式化。
- 既存の `Formal/AG/`、`Formal/Util/`、`research/lean/`、ツール群（`tools/`）、公開面（`website/`）の改修。

---

## 7. 実装計画（推奨 PR 分割順）

1. **PR 1（AC-01）**：`Formal/SHIGURE.lean`、独立公理監査コマンドとテスト、孤立 import 検査、`.github/workflows/lean.yml` 専用ジョブ。
2. **PR 2（AC-02）**：`Part1/Signature.lean`, `Part1/Syntax.lean`, `Part1/Chapter1Examples.lean`（例 1.6）。
3. **PR 3（AC-03）**：`Part1/Preservation.lean`, `Part1/Chapter1Examples.lean`（例 1.10）。
4. **PR 4（AC-04）**：`Part1/PositiveLogic.lean`（付録A 全体と理論の圏 $\mathbf{Th}$）。
5. **PR 5（AC-05）**：`Part1/Models.lean`（$\mathrm{Str}_\Sigma, \mathcal A_{\mathbb T}, \mathcal A_{\mathbb T;M_0}$, 命題 2.3）。
6. **PR 6（AC-06）**：`Part1/Pullback.lean`（定理 2.4, 系 2.4a, 構成 2.5）。
7. **PR 7（AC-07）**：`Part1/OperationWords.lean`（定理 2.6, 例 2.7）。
8. **PR 8（AC-08）**：`Part1/Lens.lean`（定義 2.8, 定理 2.9, 命題 2.10）。
9. **PR 9（AC-09）**：`Part1/Protocol.lean`（定義 2.11, 定理 2.12, 例 2.13）。
10. **PR 10（AC-10）**：`Part1/Contexts.lean`（定義 3.1–3.3, 命題 3.2, 定理 3.4–3.5）。
11. **PR 11（AC-11）**：`Part1/MarkedModules.lean`（命題 3.6, 例 3.7）。
12. **PR 12（AC-12）**：`Part1/FragmentsAndRings.lean`（定義 3.8, 例 3.10, 命題 3.11, 例 3.12）+ `AxiomAudit.lean` 最終統合。

各 PR は [Workflow guideline](../workflow/guideline.md) の PR 前チェックおよび `math-lean-review`（独立 4 lane・別モデル PR レビュー）を通過してマージする。

---

## 8. 停止条件

次のいずれかに該当した時点で実装ループを停止し、状況を報告して人間判断を仰ぐ。

1. 数学本文（第1–3章・付録A）の記述に Lean 形式化上の曖昧さ・不整合・欠落が見つかり、Tier 1 文書の判断または PRD の改訂が必要になった場合（ループ内で PRD や数学本文を編集しない）。
2. [Lean 品質基準](../aat/lean_quality_standard.md) §5.3 に該当する target statement の変更（仮定の追加・結論の弱化・対象縮小）が必要と判明した場合。
3. 同一 AC で 2 周連続して PR がマージに至らない（`stalled`）場合。
4. 独立レビューゲート（`math-lean-review` / `$prd-completion-review`）が実行不能または `Blocked` となった場合。
