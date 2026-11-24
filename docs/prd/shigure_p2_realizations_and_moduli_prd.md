# SHIGURE Lean 形式化 PRD（第II部・付録B：実現の族・Law の幾何・モジュライ）

| 項目 | 内容 |
| --- | --- |
| 状態 | Draft |
| 対象配置 | `Formal/SHIGURE.lean`, `Formal/SHIGURE/AxiomAudit.lean`, `Formal/SHIGURE/Part2/**` |
| 親計画 Issue | 未起票（着工前に GitHub Issue を起票し、第I部側の親 Issue との依存関係を設定する） |
| 数学本文（Tier 1 参照先） | [第4章](../aat/algebraic_geometric_theory/part_2/chapter_4_coefficient_realizations.md), [第5章](../aat/algebraic_geometric_theory/part_2/chapter_5_quantities_and_law_geometry.md), [第6章](../aat/algebraic_geometric_theory/part_2/chapter_6_families_and_moduli.md), [付録B](../aat/algebraic_geometric_theory/appendix_b_coefficients_and_descent.md), [第19章 19.6節（設定 19.12・補題 19.13）](../aat/algebraic_geometric_theory/part_6/chapter_19_local_reconstruction_and_finite_determination.md#196-有限ハンケル表からの最小実現), [共通記号](../aat/algebraic_geometric_theory/notation.md) |
| 適用ガイドライン | [AAT guideline](../aat/guideline.md), [Lean 品質基準](../aat/lean_quality_standard.md), [Workflow guideline](../workflow/guideline.md), [PRD guideline](guideline.md), [語彙ルール](../workflow/vocabulary.md) |
| CI 変更要否 | 不要（既存の `.github/workflows/lean.yml` ジョブ `SHIGURE build and kernel audit` が `Formal/SHIGURE/**` と `Formal/SHIGURE.lean` を自動対象とする） |

---

## 1. 問い

> 既存の `Formal/SHIGURE/Part1/**` および現行の `Formal/SHIGURE` 独立 CI・公理監査基盤の上で、`Formal/AG/`・`Formal/Util/`・`research/lean/ResearchLean/` を一切 import せずに、数学本文の第II部（第4–6章）・付録B（および第6.6節が先行参照する第19章の設定 19.12・補題 19.13）のすべての定義・構成・番号付き証明付き主張（25 件、ならびに節内の descent・相対 Spec・可換性主張）・番号付き具体例（9 件、ならびに本文中の無番号具体例・反例）を、仮定の追加や結論の弱化なしに Lean カーネルで検証できるか。

---

## 2. 現状診断

- 数学本文 `docs/aat/algebraic_geometric_theory/`（全 6 部 19 章 + 付録 A–F）は完成しており、第II部（第4–6章）と付録Bは第I部の語彙・構造・モデル・宣言文脈の上に、係数環上の実現（複製方式・テンソル方式）、固定構造上の量モデルのアフィン幾何、忠実平坦 descent、生成元付き実現のスキーム表示、商スタック、スタック上相対 $\mathrm{Spec}$、および最小実現の Grassmann 表示を構成する。
- 第 6.6 節（定理 6.12）は第 19 章 19.6 節の設定 19.12・補題 19.13 を先行参照しているが、両者の定義と線形代数の証明は第 6 章・第 17 章に依存しない自己完結した内容である。
- `Formal/SHIGURE/` 配下には `AssertStandardAxioms.lean`、`AssertStandardAxiomsTest.lean`、`AxiomAudit.lean`、`Part1/**` および入口 `Formal/SHIGURE.lean` が整備されており、`.github/workflows/lean.yml` の `SHIGURE build and kernel audit` ジョブが以下を自動検証する：
  - `lean --run .github/lean_quality/check_shigure_imports.lean`（孤立 import 検査）
  - `lake build +Formal.SHIGURE`
  - `.github/lean_quality/check_shigure_declarations.lean`（禁止構文・`debug.skipKernelTC`・全宣言の標準公理依存検査）および `test_shigure_declarations.sh`
  - `Formal/SHIGURE/AssertStandardAxiomsTest.lean` および `Formal/SHIGURE/AxiomAudit.lean`
- Lean 環境は `leanprover/lean4:v4.28.0` / `mathlib v4.28.0` であり、`Formal/SHIGURE/Part2/` は未作成である。

---

## 3. 全体設計と不変条件

### 3.1 完全独立の不変条件（`Formal/AG` 等との非依存）

- `Formal/SHIGURE/**` および `Formal/SHIGURE.lean` が import できるのは `Mathlib.*`、`Std.*`、`Lean.*`、`Formal.SHIGURE.*`（`AssertStandardAxiomsTest` を除く）のみとする（既存の `check_shigure_imports.lean` による機械検査を維持する）。
- `Formal/SHIGURE/Part2/**` からは既存の `Formal/SHIGURE/Part1/**` を再利用し、第1–3章の署名・構造・モデル・宣言文脈・生成元付き実現・多項式座標環と直接接続する。
- `Formal.lean`、`Formal/AG/`、`Formal/Util/`、`research/lean/`、`.github/workflows/lean.yml` は変更しない。

### 3.2 数学本文との整合・mathlib 接続・Lean 品質規律

- すべての新規宣言は [Lean 品質基準](../aat/lean_quality_standard.md) に従う：
  - **§1.1 material premise の三分類申告**：PR 本文で各定理の仮定を「本文由来（部・定理番号つき）」「放電済み（放電宣言名つき）」「未放電」に分類して申告する。未放電仮定を持つ定理は本 PRD の完了根拠としない。
  - **§1.2 premise 使用性**：未使用引数を残さない。
  - **§1.3–§2.3 API 接続義務と mathlib 再発明の禁止**：
    - mathlib v4.28.0 に存在する概念（`CategoryTheory`, `Coalgebra`, `MvPolynomial`, `SymmetricAlgebra`, `Ideal.Quotient`, `Localization`, `PrimeSpectrum`, `AlgebraicGeometry.Scheme`, `Scheme.Spec`, `Scheme.GlueData`, `Module.Flat`, `Module.FaithfullyFlat`, `Module.Finite`, `Module.Projective`, `RingHom.FinitePresentation`, `Matrix.GeneralLinearGroup` 等）はそのまま用いるか、やむを得ず別表現を選ぶ場合は `Implementation notes` に理由を明記し comparison 同値・関手で直接接続する。
    - mathlib v4.28.0 に直接の定義が存在しない上位概念（一般スキーム上の準連接加群/代数層、fppf 位相・fppf スタック、torsor、代数的空間・代数的スタック、相対 $\mathrm{Spec}$ 等）は `Formal/SHIGURE/Part2/` 内に小さく定義し、アフィン試験スキーム $\mathrm{Spec}\,R$ 上で mathlib の `Module` / `Algebra` / `Scheme.Spec` / `Scheme.GlueData` への明示的な比較同値・接続定理を必ず備える。
    - 本文がスキーム論の標準事実として引用する命題（例：付録 B.3 の「平坦かつ局所有限表示なスキーム射の開性」、第 6.4 節の「滑らかな射の平坦性・基底変換安定性・fppf 局所性」）についても、`axiom`・`sorry`・未放電の引数仮定で済ませず、mathlib 定理の直接利用または `Formal/SHIGURE/Part2/` 内での完全証明により放電する。
  - **§1.4 instance ペア**：新規の `Prop` 述語や構造に対し、肯定・否定の双方の witness を備える（本文の番号付き 9 例および無番号具体例・反例を直接形式化する）。
  - **§2.1–§2.5**：小さい定義、data と `Prop` の分離、definitional escape 禁止、no-unfold API（`ext` / constructor / destructor / 特徴づけ補題を定義と一体で提供）、自明でない表現選択への `Implementation notes` 記載。
  - **§4.1 標準公理検査**：許容するカーネル公理は `propext`, `Classical.choice`, `Quot.sound` のみ。`axiom`, `admit`, `sorry`, `unsafe`, `native_decide`, `debug.skipKernelTC` を禁止する。
- **基礎環・集合論・宇宙の規約**（[共通記号](../aat/algebraic_geometric_theory/notation.md)・第4章 4.1 節）：
  - 基礎環 $k$ は単位元を持つ任意の可換環とし、零環を含める（非零や連結性が必要な主張では本文どおり明示的に仮定する）。環射は単位元を保つ。
  - 担体集合、量添字集合 $J$、演算族、Law 族、生成子・関係添字集合 $H_0, H_1$ は本文で有限と明記された箇所（例：第 6 章の sort 集合 $S_0$、各演算の arity、設定 19.12 の有限単項操作など）を除き、任意の小さい集合（固定した宇宙 `Type u`）として扱い、勝手な有限化・固定化を行わない。
- **Lean build 運用（hard rule）**：[AAT guideline](../aat/guideline.md) に従い、ローカル確認は単一ファイル `lake env lean <target-file>` および必要時の対象モジュール `lake build <module>` とし、フル `lake build` は CI（`lake build +Formal.SHIGURE`）で行う。サブエージェントの `lake build` は全面禁止する。

### 3.3 推奨モジュール配置

```text
Formal/
├── SHIGURE.lean
└── SHIGURE/
    ├── AxiomAudit.lean
    ├── Part1/ ...
    └── Part2/
        ├── AffineFoundations.lean        -- 付録 B.1: 補題 B.1, B.2, B.3
        ├── CopyingCoalgebra.lean         -- 第4章 4.1–4.3: 定義 4.1, 構成 4.2, 定理 4.3, 例 4.4, 定義 4.5, 定理 4.6, 例 4.7
        ├── TensorRealizations.lean       -- 第4章 4.4: 構成 4.8, 定理 4.9, 命題 4.10, 例 4.11
        ├── RealizationRecovery.lean      -- 第4章 4.5: 定理 4.12, 局所充足例, 局所分裂複製対象の Zariski descent, 命題 4.13
        ├── QuantityModels.lean           -- 第5章 5.1–5.3: 定義 5.1, 構成 5.2, 補題 5.3, 定理 5.4, 定理 5.5, 例 5.6, 例 5.7
        ├── QuantityTransport.lean        -- 第5章 5.4–5.5: 定理 5.8, 命題 5.9, 例 5.10, 制限可換性, 定理 5.11, 例 5.12
        ├── FaithfullyFlatDescent.lean    -- 付録 B.2: 補題 B.4, 補題 B.5, 式 (B.1)–(B.3)
        ├── SchemesAndRelativeSpec.lean   -- 付録 B.3: 一般スキーム fppf descent, 補題 B.6, 補題 B.7, スタック上相対 Spec
        ├── RealizationStack.lean         -- 第6章 6.1: 定義 6.1, 補題 6.2, 式 (6.1)
        ├── MarkedCharts.lean             -- 第6章 6.2–6.3: 定義 6.3, 構成 6.4, 定理 6.5, 例 6.6, 式 (6.2)–(6.3)
        ├── QuotientStack.lean            -- 第6章 6.4: 定理 6.7, 自己同型群スキーム, 階数直和, 例 6.8, 式 (6.4)
        ├── StackRelativeSpec.lean        -- 第6章 6.5: 定義 6.9, 定理 6.10, 式 (6.5)–(6.6), 非単射引戻し例
        └── MinimalRealization.lean       -- 第6章 6.6 / 19.6節: 設定 19.12, 補題 19.13, 定理 6.12
```

（Part 1 と同様に、1 ファイルが過大になる場合は責務ごとに細分化し、`Formal/SHIGURE/Part2/<Topic>.lean` を集約入口として `Formal/SHIGURE.lean` から到達可能にすること。）

---

## 4. 一次仕様（Target Statements）と受け入れ条件（Acceptance Criteria）

本節を本 PRD における **target statement の一次仕様**（[Lean 品質基準](../aat/lean_quality_standard.md) §5）とする。各 AC の数学的主張・仮定・結論の正典は対応する数学本文の番号付き項目であり、仮定の追加・結論の弱化・対象縮小（有限化・固定化・非零環への無断限定等）を禁止する。

### AC-01: 付録 B.1（開閉分割と冪等元・多項式/対称代数/Spec・係数変更と方程式）

- **補題 B.1（開閉分割と冪等元）**：任意の可換環 $R$ について、(1) 冪等元 $e \in R$ と $\mathrm{Spec}\,R$ の開閉集合の $e \mapsto D(e)$ による一対一対応、(2) 有限個の互いに素な開閉集合による $\mathrm{Spec}\,R$ の分割と、和が $1$ で互いに直交する冪等元の有限族との一対一対応を証明する（mathlib `PrimeSpectrum` / `Scheme.Spec` 接続）。
- **補題 B.2（任意集合の多項式・対称代数・Spec）**：任意の小さい集合 $L$ に対する自然な全単射 $\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(k[t_l\mid l\in L], R) \cong R^L$（`MvPolynomial`）、任意の $k$-加群 $Q$ に対する自然な全単射 $\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(\mathrm{Sym}_k Q, R) \cong \mathrm{Hom}_k(Q, R)$（`SymmetricAlgebra`）、および任意の $k$-スキーム $T$ と可換 $k$-代数 $B$ に対する自然な全単射 $\mathrm{Hom}_k(T, \mathrm{Spec}\,B) \cong \mathrm{Hom}_{k\text{-}\mathrm{Alg}}(B, \Gamma(T, \mathcal O_T))$ を証明する。
- **補題 B.3（係数変更と方程式）**：任意の環射 $R \to R'$ に対し（平坦性不要）、直和・テンソル積・余核・対称代数が係数変更 $-\otimes_R R'$ と自然同型で可換すること、および $R$-代数 $A$ とイデアル $I=(f_i)\subseteq A$ に対する自然な $R'$-代数同型 $(A/I)\otimes_R R' \cong (A\otimes_R R')/(f_i\otimes 1 \mid i)$（像イデアルによる商）を証明する。

### AC-02: 第4章 4.1–4.3（係数的実現方式・複製余代数・定理 4.3・例 4.4・台プロファイル・定理 4.6・例 4.7）

- **定義 4.1（係数的実現方式）**：4 つの構成規則（許容担体と対応規則、原始構造の構成規則、係数変更規則、Law 解釈規則）と、各係数 $R$ における意味圏 $\mathcal A_{\mathbb T,\sigma}(U,R)$（`CategoryTheory.Category` インスタンス）、Zariski 局所分裂な複製方式・テンソル方式の定義、および複製方式における Zariski 層上の正の式・Law（部分層包含）の解釈規則を定める。
- **構成 4.2（複製と状態の族）**：任意の集合 $X$ と可換環 $R$ に対し、自由 $R$-加群上の余代数 $C_R(X)=\bigoplus_{x\in X}Re_x$（$\Delta(e_x)=e_x\otimes e_x,\ \epsilon(e_x)=1$、mathlib `Coalgebra` 接続）、定数 $R$-スキーム $\underline X_R = \coprod_{x\in X}\mathrm{Spec}\,R$、集合写像から誘導される余代数射・スキーム射、および同型 $C_R(X\times Y)\cong C_R(X)\otimes_R C_R(Y)$（空積は $R$）を構成する。
- **定理 4.3（複製表示のすべての射）**：任意の集合 $X,Y$ と可換環 $R$ に対する自然な全単射 $\mathrm{Coalg}_R(C_R(X),C_R(Y)) \cong \mathrm{Hom}_{R\text{-}\mathrm{Sch}}(\underline X_R,\underline Y_R) \cong$ 式(4.1)（$a_{xy}^2=a_{xy},\ a_{xy}a_{xz}=0\ (y\ne z),\ \sum_y a_{xy}=1$）を満たす各行有限台の係数族 $(a_{xy})$ を構成し、恒等・合成・係数変更との整合を証明する。さらに、$R\ne 0$ かつ冪等元が $0,1$ のみのとき $\mathrm{Set}(X,Y)$ と全単射になること、および極端な場合（$X=\varnothing$、$Y=\varnothing \land X\ne\varnothing \land R\ne 0$、$R=0$）を証明する。
- **例 4.4（Boolean 論理積と反復する変数）**：$B=\{0,1\}$ 上の線形化論理積 $m(e_a\otimes e_b)=e_{a\wedge b}$ で $m\Delta=\mathrm{id}$ が成り立つ一方、$R=\mathbb Z, v=2e_1$ で $m(v\otimes v)=4e_1\ne 2e_1$ となることを証明する。
- **定義 4.5（台プロファイル）**：各 $x\in X$ に有限部分集合 $F_x\subseteq Y$（空集合許容）を割り当てる台プロファイル $F$、アフィンスキーム $P_F$、$F\le F'$ での閉埋込み $P_F\to P_{F'}$、および有向性を構成・証明する。
- **定理 4.6（すべての台プロファイルによる回復と合成）**：任意の $k$-代数 $R$ での自然な全単射 $\mathop{\mathrm{colim}}_F P_F(R) \cong \mathrm{Coalg}_R(C_R(X),C_R(Y))$、および式(4.2) による合成スキーム射 $P_F\times_k P_H \to P_K$ と、台プロファイル拡大・恒等射・結合律・係数変更との整合を証明する。
- **例 4.7（無限出力における全域性）**：$X=Y=\mathbb N$ の恒等写像が $F_n=\{n\}$ で表示される一方、全入力に共通する有限出力集合が存在しないこと、および零行が任意の有限個の冪等性・直交性条件を満たすが和 1 の条件を満たさないことを証明する。

### AC-03: 第4章 4.4（テンソルによる係数変更・定理 4.9・命題 4.10・例 4.11）

- **構成 4.8（テンソルによる係数変更）**：各 sort の $k$-加群 $M_s$ と有限 arity 多重線形演算 $\mu_e:\bigotimes_i M_{s_i}\to M_t$（0 引数＝指定元含む）に対し、$M_{s,R}=M_s\otimes_k R$、式(4.3) の拡張演算、環射 $\alpha:R\to R'$ に沿う係数変更、単位同型・結合同型の 3 段階整合（および任意 $R$-加群実現の係数変更）、線形・多重線形量の延長、ならびに普遍単射な部分加群 $D\hookrightarrow\bigotimes_i M_{s_i}$（分裂が十分条件であることの証明含む）による部分操作の延長を構成・証明する。
- **定理 4.9（二つの方式の自然な比較）**：任意の $k$-加群 $M$ と $k$-代数 $R$ に対し、式(4.4) の写像 $\iota_{M,R}:\underline{|M|}_k(R)\to M\otimes_k R$（スカラー sort の $\iota_{k,R}$ 含む）を構成し、環射に関する自然性、定数点 $m\mapsto m\otimes 1$、加法・スカラー作用・線形および多重線形演算（反復入力含む）との可換性を証明する。
- **命題 4.10（テンソル方式で Law が延びる条件）**：全域多重線形演算から構成される二つの有限項 $t,t'$ に対し、任意の有限個の $m_{ij}\in M_{s_i}$ と形式変数 $z_{ij}$ に関する式(4.5)（$M_u\otimes_k k[z_{ij}]$ 上での零等式）が、すべての $k$-代数 $R$ のすべての入力での拡張等式成立と同値であることを証明する。さらに、恒等・置換・原始演算・テンソル積・合成・有限和・スカラー倍から構成した同型の二つのテンソル写像が元の加群上で等しければ任意の係数変更後も等しいことを証明する。
- **例 4.11（点上の等式と微小方向）**：$k=\mathbb F_p$ で全元が $x^p=x$ を満たすが $R=k[t]$ の $t$ および双対数環 $R=k[\varepsilon]/(\varepsilon^2)$ の $\varepsilon$ で式(4.5) が成り立たないこと、さらに $k[\varepsilon]/(\varepsilon^2)$ の冪等元が $0,1$ に限られ $\varepsilon$ が比較写像 $\iota_{k,R}$ の像に属さないことを証明する。

### AC-04: 第4章 4.5（定理 4.12・局所充足例・局所分裂複製対象の Zariski descent・量読取り・命題 4.13）

- **定理 4.12（原始構造を含む複製実現の回復）**：第1章の任意の小さい理論 $\mathbb T$ と元の構造 $A$（固定 sort・指定値含む）に対する複製実現（$\underline{X_s(A)}_R, \underline{r_A}_R, \underline{D_p^A}_R$ 等と 4.1 節の層上解釈）について、(1) 項の定義域・値グラフ・正の式の解釈が元の構造の対応部分集合の下線定数部分層に一致し、元の構造で成立する全 Law がすべての $k$-代数 $R$ で成立すること、(2) $R$ が連結かつ非零ならば構造保存射が元の構造保存射と全単射に対応すること（固定 sort 恒等・指定値・量保存の回復含む）、(3) 連結非零 $R$ の下で、大域分裂対象からなる $\mathcal A_{\mathbb T,\mathrm{copy}}(U,R)$ の充満部分圏が元の意味圏 $\mathcal A_{\mathbb T}$ と圏同値であること、(4) 係数変更が原始構造・射の恒等/合成・宣言制限と可換すること、の 4 点を証明する。
- **局所充足の例**：$\{0,1\}$ 上の Law $\top\vdash_x (x=0\vee x=1)$ について、非零環 $k$ と $R=k\times k$ の非定数点が、大域切断の集合上では選言を満たさないが Zariski 開被覆上の層解釈では成立することを証明する。
- **局所分裂な複製対象の係数変更と Zariski descent**：Zariski 局所分裂な複製実現と構造保存射について、ファイバー積による係数変更（Law 保存・単位/結合同型の整合含む）と、Zariski 被覆上の対象（cocycle 付き）および整合局所射の有効 descent を証明する。
- **Atom と量のスカラー読み取り**：元の量 $q:X\to k$ のスカラー読み取り $\underline X_R\to\underline{|k|}_R \xrightarrow{\iota_{k,R}} R$（$(a_x)\mapsto \sum_x a_x q(x)$）を構成し、環射 $\mathbb Z\to\mathbb F_p$ が異なる元の値を同一スカラーへ送ること（固定値 sort との違い）を証明する。
- **命題 4.13（テンソル実現の対象とすべての線形射）**：構成 4.8 の対象を $R=k$ で読むと単位同型で元の加群・演算が回復すること、全 $k$-代数 $R$ に自然な $R$-線形構造保存射の族全体が元の構造保存線形射全体と全単射に対応する（恒等・合成整合）こと、固定 $R$ での射が全構造保存 $R$-線形射であることを証明する。あわせて、双対数環 $k[\varepsilon]/(\varepsilon^2)$ 上の線形射 $z\mapsto\varepsilon z$ が体 $k$ 上の射の係数変更から得られないことを証明する。

### AC-05: 第5章 5.1–5.3（固定構造上の量モデル・構成 5.2・補題 5.3・定理 5.4・定理 5.5・例 5.6–5.7）

- **定義 5.1（固定定義域の量と等式 Law）**：基礎環 $k$・固定構造 $S$・小さい量添字集合 $J$・小さい定義域 $D_j(S)$・量モデル候補 $q_j:D_j(S)\to R$・等式 Law（$E_\ell(S), t_\ell, t'_\ell$）を定義し、環射による前合成が関手 $\mathrm{QMod}_S : k\text{-}\mathrm{Alg}\to\mathrm{Set}$ を定めることを証明する。
- **構成 5.2（量の座標と元の式の評価）**：$L_S=\coprod_{j\in J}D_j(S)$、式(5.1) の自由加群 $Q_S$ と多項式環 $A_S=\mathrm{Sym}_k Q_S \cong k[t_{j,x}]$、普遍量 $q_j^{\mathrm{univ}}(x)=t_{j,x}$、式(5.2) の普遍残差 $\rho_\ell(e)$（線形写像表示 $C_k(E_\ell(S))\to A_S$ 含む）と残差イデアル $I_S$、周囲空間 $X_S=\mathrm{Spec}\,A_S$、Law を課した空間 $M_S=\mathrm{Spec}(A_S/I_S)$、閉埋込み $i_S:M_S\hookrightarrow X_S$ を構成する。
- **補題 5.3（元の式と普遍残差の評価）**：任意の量モデル候補 $q$ に対する一意な $k$-代数射 $\mathrm{ev}_q:A_S\to R$、式(5.3) $\mathrm{ev}_q(\rho_\ell(e))=t_\ell(q,e)-t'_\ell(q,e)$、および係数変更と定義可能な状態項代入（定理 1.8 と接続）に関する自然性を証明する。
- **定理 5.4（量・Law モデルの相対表現）**：任意の小さい定義域族・Law 族に対する式(5.4) の自然な全単射 $\mathrm{QMod}_S(R)\cong\mathrm{Hom}_{k\text{-}\mathrm{Alg}}(A_S/I_S,R)\cong\mathrm{Hom}_k(\mathrm{Spec}\,R,M_S)$、普遍モデル $(\overline t_{j,x})$、および一般の試験 $k$-スキーム $T$ 上の大域切断版 $\mathrm{QMod}_S(T)\cong\mathrm{Hom}_k(T,M_S)$ を証明する。
- **定理 5.5（Lawful locus への一意な因子分解）**：任意の試験スキーム $T$ と射 $p:T\to X_S$ について、(1) 全必須残差が $\mathcal O_T$ の切断として $0$、(2) 引き戻し写像 $p^{-1}\widetilde I_S\to\mathcal O_T$ の像が生成するイデアル層が $0$、(3) $p=i_S\circ\bar p$ となる $\bar p:T\to M_S$ の一意存在、の三条件同値を証明する。
- **例 5.6（可換代数と対称代数の回復）**：任意の可換 $k$-代数 $B$ に対し $A_B/I_B\cong B$、任意の $k$-加群 $N$ に対し $A_N/I_N\cong\mathrm{Sym}_k N$ となることを証明する。
- **例 5.7（逆元と冪零方向）**：(a) $k[x,y]/(xy-1)\cong k[x,x^{-1}]$、(b) $k[t]/(t^2)$ における $t=0$ 上の双対数環持ち上げ $t\mapsto a\varepsilon$、および普遍余法加群 $I/I^2=(t^2)/(t^4)$ を $t=0$ の点へテンソルすると $k$ に同型になることを証明する。

### AC-06: 第5章 5.4–5.5（定理 5.8・命題 5.9・例 5.10・制限可換性・定理 5.11・例 5.12）

- **定理 5.8（構造射による反変な量の比較）**：量定義域写像 $h_j$ と Law 入力写像 $h_\ell$ を誘導する構造射 $h:S\to S'$ に対し、式(5.5) の $k$-代数射 $\phi_h:A_S\to A_{S'}$ と包含 $\phi_h(I_S)\subseteq I_{S'}$、誘導スキーム射 $M(h):M_{S'}\to M_S$、任意係数 $R$ での引き戻し $q'_j\mapsto q'_j\circ h_j$ との一致、および恒等・合成・係数変更との可換性を証明する。
- **命題 5.9（量の一致を課す対応空間）**：$h_j$ のみ運ぶ $h$ に対するアフィンスキーム $Z_h$ を構成し、全試験スキーム上で $q=h^*q'$ を満たす対 $(q,q')$ を表現すること、第二射影 $Z_h\to M_{S'}$ が閉埋込みであり $Z_h\cong\mathrm{Spec}(A_{S'}/(I_{S'}+A_{S'}\phi_h(I_S)))$ であること、および $Z_h$ が $M_{S'}$ 全体からの射のグラフになることと $\phi_h(I_S)\subseteq I_{S'}$ の同値性を証明する。
- **例 5.10（Law 入力の保存が必要になる場合）**：$D(S)=\{a\}, D(S')=\{b\}, h(a)=b, E(S)=\{a\}, E(S')=\varnothing$ と $q(x)=0$ について、$M_S\cong\mathrm{Spec}\,k$、$M_{S'}\cong\mathrm{Spec}\,k[t]$、$Z_h\to M_{S'}$ が $t=0$ の閉部分スキームを与えること、および $k\ne 0$ で $q'(b)=1$ の引き戻しが $S$ の Law を満たさないことを証明する。
- **宣言制限と係数変更の可換性**：第3章の宣言制限 $S|_U$ と係数変更 $R$（特に局所化による開制限含む）について、比較射 $(A_{S|U}/I_{S|U})\otimes_k R\to (A_S/I_S)\otimes_k R$ が両順序で一致することを証明する。
- **定理 5.11（正則な拡張の分類）**：任意の小さい集合 $D,X$、$q:D\to k^X$、$\varepsilon:D\to k$ に対し、有限単項式集合 $F$ ごとのアフィンスキーム $E_F$（式(5.6)）、閉埋込み $E_F\to E_{F'}$、余極限関手 $E=\mathop{\mathrm{colim}}_F E_F$ を構成し、任意の $k$-代数 $C$ における $E(C)$ と全 $C$-代数 $R$ に自然な写像族 $f_R:R^X\to R$（$f_C(q(d)_C)=\varepsilon(d)_C$）との自然な全単射を証明する。
- **例 5.12（非一意性と不存在）**：本文の 4 事例すべてを証明する：(1) $k=\mathbb F_p$ 上の $P=t$ と $P=t^p$ の非一意性および $k[\eta]/(\eta^2)$ 上の分離、(2) $k=\mathbb Q$ 上の $\varepsilon(0)=1, \varepsilon(d)=0\ (d\ne 0)$ における $E(\mathbb Q)=\varnothing$、(3) $D=k^X, q=\mathrm{id}$ における無限体上の一意性および有限体 $\mathbb F_N$ 上の消滅イデアル $(t_x^N - t_x\mid x\in X)$ の決定、(4) $k=\mathbb Z, D=\mathbb Z, X=\{x\}, q(n)=2n, \varepsilon(n)=n, F=\{t\}$ での $E_F\cong\mathrm{Spec}\,\mathbb Z[1/2]$ のスキーム非空性と $E_F(\mathbb Z)=\varnothing$。

### AC-07: 付録 B.2（忠実平坦な係数 descent：補題 B.4・補題 B.5）

- 忠実平坦な環射 $A\to B$（mathlib `Module.FaithfullyFlat` 接続）と $B$-加群の descent データ $(N,\theta:N\otimes_A B\xrightarrow{\sim} B\otimes_A N)$（式(B.1) のコサイクル条件 $\theta_{12}\theta_{01}=\theta_{02}$）および descent データの圏を構成する。
- **補題 B.4（加群とすべての写像の有効 descent）**：忠実平坦射 $A\to B$ に対する $A$-加群の圏と descent データの圏の圏同値（`CategoryTheory.Equivalence`）、式(B.2) の等化子 $M=\{n\in N\mid \theta(n\otimes 1)=1\otimes n\}$ と比較同型 $B\otimes_A M\xrightarrow{\sim} N$、および式(B.3) の基本恒等式を証明する。
- **補題 B.5（有限局所自由性、テンソルと演算）**：アフィン上の有限局所自由加群が有限表示・平坦・有限射影であること、忠実平坦射 $A\to B$ に沿って有限生成性・有限表示性・平坦性・有限局所自由性・一定階数 $n$ が降下すること、ならびにテンソル積・線形/多重線形演算・指定元・同型テンソル式等号・構造保存写像（全射性含む）が同じ descent で降下することを証明する。

### AC-08: 付録 B.3（一般スキームの fppf descent・補題 B.6・補題 B.7・スタック上相対 Spec）

- 準連接加群・準連接代数を構成し、各アフィン開集合上の $\widetilde N$ 表示とあるアフィン開被覆上の局所表示の同値性を証明する。
- 平坦かつ局所有限表示なスキーム射の開性とアフィン底の準コンパクト性を用いた有限アフィン忠実平坦細分により、一般のスキーム上の fppf 被覆に対する準連接加群・有限局所自由加群・原始演算・構造保存射の有効 descent を証明する（Zariski 被覆における整合切断構成との一致を含む）。
- **補題 B.6（開チャートの接着）**：スキーム族 $(U_i)$・開部分スキーム $U_{ij}\subseteq U_i$・恒等/両逆/三重交差コサイクルおよび重なり開集合対応を満たす同型 $\varphi_{ij}:U_{ij}\xrightarrow{\sim} U_{ji}$ からスキーム $M$ を接着し（`Scheme.GlueData` 接続）、同じコサイクル条件を満たす加群層とその射の貼り合わせを証明する。
- **補題 B.7（準連接代数の相対 Spec）**：スキーム $T$ 上の準連接 $\mathcal O_T$-代数 $\mathcal C$ に対するアフィン $T$-スキーム $\mathrm{Spec}_T\mathcal C$ を構成し、任意のスキーム射 $g:T'\to T$ に対する自然な全単射 $\mathrm{Hom}_T(T',\mathrm{Spec}_T\mathcal C)\cong\mathrm{Hom}_{\mathcal O_{T'}\text{-}\mathrm{Alg}}(g^*\mathcal C,\mathcal O_{T'})$ と、任意の基底変換との可換性を証明する。
- **fppf スタック上の相対 Spec 拡張**：fppf スタック $\mathcal B$ 上の準連接代数 $\mathcal C$ に対し、各試験スキーム $T\to\mathcal B$ に補題 B.7 を適用して得られる族が fppf スタックをなし、固定構造 $b$ のファイバーが補題 B.7 のアフィン $T$-スキームに一致することを証明する。

### AC-09: 第6章 6.1（実現の族・多項式 Law・補題 6.2）

- **定義 6.1（実現の族と多項式的な入力）**：最大部分 groupoid $\mathcal M_{\mathbb T,\sigma}(U,R)=\mathcal A_{\mathbb T,\sigma}(U,R)^{\simeq}$（`CategoryTheory.Core` 接続）の擬関手構造、有限 sort 集合 $S_0$・階数 $n_s\ge 0$・小さい有限 arity 多重線形演算族式(6.1)・小さい Law 族による実現圏と最大部分 groupoid $\mathrm{Real}_{\boldsymbol n}(T)$ を定義する。テンソル式 Law に加え、多項式 Law の構文・意味・自由チャート上での単項式係数展開・多項式 Law 成立と全単項式係数零の同値性・基底変更に対する生成イデアルの座標独立性・任意環射との可換性、および引き戻しによる Law 保存を証明する。
- **補題 6.2（加群・演算・射の係数 descent）**：定義 6.1 の実現とすべての構造保存射の Zariski 被覆および fppf 被覆に関する有効 descent と、$\mathrm{Real}_{\boldsymbol n}$ が fppf スタックであることを証明する。あわせて、第3章の宣言方向制限と係数方向引き戻しが自然な同型の下で交換することを証明する。

### AC-10: 第6章 6.2–6.3（生成元付き実現・構成 6.4・定理 6.5・例 6.6）

- **定義 6.3（生成元付き実現と基底付き実現）**：整数 $m_s\ge n_s$ に対する全射マーキング $\pi_s:\mathcal O_T^{m_s}\twoheadrightarrow E_s$、同型類集合 $\mathrm{Mark}_{\boldsymbol m,\boldsymbol n}(T)$（小さい宇宙での集合性、マーキングを保つ自己同型が恒等射に限ること、groupoid との圏同値）、アフィン上での核 $K_s=\ker\pi_s\subseteq R^{m_s}$ と商 $R^{m_s}/K_s$ による表示および分裂短完全列による任意係数変更との一致、ならびに基底付き実現（$b_s:\mathcal O_T^{n_s}\xrightarrow{\sim} E_s$）を構成・証明する。
- **構成 6.4（基底を選んだ方程式）**：チャート添字 $I=(I_s)$、生成元行列 $P_s^I$、式(6.2) の周囲環 $A_I$・残差イデアル $J_I$・商環 $B_I$・アフィンチャート $U_I=\mathrm{Spec}\,B_I$、普遍自由実現を構成し、$I_s$ 番目生成元が全域基底をなす生成元付き実現の関手を $U_I$ が表現することを証明する。
- **定理 6.5（生成元付き実現のスキーム表示）**：基本開集合 $D(d_{IJ})$（$d_{IJ}=\prod_{s\in S_0}\det C_s$、階数 0 は行列式 1）上の式(6.3) の遷移開同型（テンソル式および多項式 Law の残差イデアルの一致、第三チャートとの重なり開集合の対応、三重交差コサイクル・両逆条件）、補題 B.6 による接着スキーム $M_{\boldsymbol m,\boldsymbol n}$ と普遍実現、および任意の試験 $k$-スキーム $T$ での自然な全単射 $\mathrm{Hom}_k(T, M_{\boldsymbol m,\boldsymbol n})\cong \mathrm{Mark}_{\boldsymbol m,\boldsymbol n}(T)$ を証明する。
- **例 6.6（二つの生成元を持つ階数 1 の商と局所基底）**：階数 1・2 生成元（演算なし、および単項演算 $N=0$ を課した場合）の接着スキームが射影直線 $\mathbb P^1_k$ に同型であること、および全射 $(2,3):\mathbb Z^2\twoheadrightarrow \mathbb Z$ が単一の基底チャートには全域で収まらないが $D(2)$ 上の $(1,3/2)$ と $D(3)$ 上の $(2/3,1)$ で $\mathrm{Spec}\,\mathbb Z$ を覆い重なり上で貼り合うことを証明する。

### AC-11: 第6章 6.4（商スタック・定理 6.7・自己同型・例 6.8・階数直和）

- 代数的空間・代数的スタック・スキーム射の滑らかさ（局所有限表示＋冪零閉埋込みに対する局所持ち上げ）・表現可能な射およびその滑らかさを定義し、必要な標準性質（滑らか $\implies$ 平坦、基底変換安定性、fppf 局所性等）を証明する。
- 基底付き実現のアフィンスキーム $X_{\boldsymbol n}$ と $G_{\boldsymbol n}=\prod_{s\in S_0}\mathrm{GL}_{n_s,k}$ の式(6.4) による右作用（$X_{\boldsymbol n}$ を保つこと、右作用公理）を構成・証明する。
- **定理 6.7（実現 groupoid と商スタック）**：すべての試験スキームにおける自然な groupoid 同値 $\mathrm{Real}_{\boldsymbol n}\simeq [X_{\boldsymbol n}/G_{\boldsymbol n}]$（フレーム torsor $P_E$ と右同変射の構成、および torsor の fppf 自明化＋補題 6.2 による逆構成）、対角射のスキーム表現可能性、滑らかな全射アトラス $X_{\boldsymbol n}\to\mathrm{Real}_{\boldsymbol n}$ による代数的スタック性、およびマーキング忘却射 $M_{\boldsymbol m,\boldsymbol n}\to\mathrm{Real}_{\boldsymbol n}$ の表現可能・滑らか・全射性を証明する。
- **自己同型群スキームと階数直和**：実現 $E$ の自己同型群スキーム $\mathrm{Aut}(E)\subseteq \prod_s\mathrm{GL}(E_s)$ がフレーム上で式(6.4) の固定化群となること（マーキング保持時の自明性との対比）、および階数を固定しない有限局所自由実現族の直和分解 $\coprod_{\boldsymbol n\in\mathbb N^{S_0}}\mathrm{Real}_{\boldsymbol n}$ を証明する。
- **例 6.8（階数 1 の加群の自己同型と冪零演算）**：階数 1・演算なしの場合の $\mathrm{Real}_{(1)}\simeq B\mathbb G_m$（例 6.6 の $\mathbb P^1_k \to B\mathbb G_m$ との接続）、および単項演算 $N$ に $N^2=0$ を課した場合の $\mathrm{Real}_{(1),N^2=0}\simeq [\mathrm{Spec}(k[z]/(z^2))/\mathbb G_m]$ と双対数環上の持ち上げ $N=a\varepsilon$ を証明する。

### AC-12: 第6章 6.5（構造の底と量の原始型・定理 6.10・検証例）

- **定義 6.9（構造の底と、量・Law の原始型）**：表現可能な fppf 全射 $p:X\to\mathcal B_\sigma$ を持つ底 fppf スタック $\mathcal B_\sigma$（特に $\mathrm{Real}_{\boldsymbol n}$ が条件を満たすこと）、加群側および fppf 局所分裂な集合側の原始担体、量の型（$\mathcal O$・$E_s$・$D_j$ 自由型・小直和・有限テンソル積・線形式 $d:P_1\to P_0$ の余核、式(6.5) の表示と本文表の 4 型すべての普遍性対応）、Law の指定、構造同型に伴う比較写像 $h_Q:Q_b\to Q_{b'}$（集合型の直交冪等元表示含む）、残差イデアル $I_b\subseteq \mathrm{Sym}_R Q_b$（全単項式係数、生成族独立性・$\psi_h(I_b)=I_{b'}$・開閉分割対応・Law 充足との同値性）を構成・証明する。
- 6.5 節の残差計算例：線形量 $q:R^2\to R$ の $q(v)^2=0$ で交差項 $2t_1 t_2$ が生成元に入ること、階数 1 の $q(v)^2=q(v)$ の生成イデアルが $(t)$ であること、および指定切断 $c$ による $q(c)=1$ が構造同型で保存されることを証明する。
- **定理 6.10（構造のスタック上の量・Law の相対幾何）**：準連接加群 $Q$、平坦 fppf site 上の準連接イデアル $I\subseteq\mathrm{Sym}\,Q$ と商代数 $\mathcal C=\mathrm{Sym}\,Q/I$、任意の試験射 $b:T\to\mathcal B_\sigma$ への引き戻し $b^*I$・$\iota_b$・像イデアル $I_b=\mathrm{im}(\iota_b)$・$b^*\mathcal C=\mathrm{Sym}_{\mathcal O_T}(b^*Q)/I_b$、および式(6.6) の相対 $\mathrm{Spec}$ $\mathcal L=\mathrm{Spec}_{\mathcal B_\sigma}\mathcal C$ を構成し、任意の $T\to\mathcal B_\sigma$ への引き戻しのアフィン表現性、ならびに被覆および生成子・関係表示からの独立性（量・関係・Law 索引の有限性不要）を証明する。
- 6.5 節の検証例：(a) 非零環 $k$ 上 $I=(at)\subset k[a,t]$ の $a=0$ への引き戻しで $I\otimes_{k[a]} k\ne 0$ だが像イデアルが $0$ であり商代数が $k[t]$ になること、(b) 固定集合を底とした $T=\mathrm{Spec}\,k$ ファイバーが定理 5.4 に一致することを証明する。

### AC-13: 第6章 6.6（設定 19.12・補題 19.13・定理 6.12：最小実現の Grassmann 表示）

- **設定 19.12（入力・操作・観測と語の加群）**：可換基礎環 $k$、有限 sort 集合 $S_0$、有限単項操作 $e:s(e)\to t(e)$、非負整数 $p_s,q_s,n_s$（$N=\sum_s n_s\ge 1$）、試験 $k$-スキーム $T$ 上の実現 $(E_s, i_s, T_e, o_s)$ と線形 Law、有限自由加群 $P_{s,r}, Q_{s,r}$、到達写像 $R_{s,r}$・観測写像 $O_{s,r}$、および全語到達写像・全語双対観測写像の全射性による最小実現を定義する。
- **補題 19.13（語長 $N-1$ での到達と双対観測）**：最小実現であることと各 $s$ の $R_{s,N-1}$ および $O_{s,N-1}^\vee$ の全射性との同値性、任意係数変更での保存、実現スタックの開条件性、および $O_{s,N-1}$ の局所分裂単射性を証明する。あわせて、19.6 節の反例（$\mathbb Z$ 上階数 1・$i=1$・操作なし・$o=2$ で $O$ は単射だが $O^\vee$ が全射でなく $\mathbb F_2$ への係数変更で零になること）を証明する。
- **定理 6.12（最小実現の Grassmann 表示）**：$d=N-1$ に対し Grassmann スキームの積 $G=\prod_{s\in S_0}\mathrm{Gr}_{n_s}(P_{s,d+1})$（構成 6.4・定理 6.5 の特殊構成、$n_s>\mathrm{rank}\,P$ で空スキーム・$n_s=0$ で唯一零商）、短い語制限全射の開部分スキーム $G^\circ$、$\pi_t\tau_e|_{K_{s,d}}=0$ の閉零点スキーム上の観測ベクトル束・Law 閉条件・長さ $d$ 以下の双対観測開条件によってスキーム $M_{\boldsymbol n}^{\min}$ を構成し、任意の試験スキームと任意の係数変更に対して普遍実現の引き戻しが最小実現の groupoid と圏同値を与えることを証明する。

### AC-14: 統合エントリポイント・最終公理監査・孤立検査

- AC-01〜AC-13 の全モジュールを `Formal/SHIGURE.lean` から到達可能にし、すべての主定理・命題・補題・系・具体例定理を `Formal/SHIGURE/AxiomAudit.lean` に登録する。
- CI ジョブ `SHIGURE build and kernel audit`（`.github/workflows/lean.yml`）において、孤立 import 検査（0 件）、`lake build +Formal.SHIGURE`、全宣言の構文・カーネル依存検査、および `AssertStandardAxiomsTest.lean` / `AxiomAudit.lean`（標準公理のみ）がすべて合格していること。

---

## 5. Failure Contract（失敗判定条件）

次のいずれかに該当した場合、本 PRD は**未達（Reject）**とする。

1. `Formal/SHIGURE/` または `Formal/SHIGURE.lean` が `Formal.AG`・`Formal.Util`・`ResearchLean` のいずれかを import している。
2. `Formal/SHIGURE/` 配下に `sorry`・`admit`・`axiom`・`unsafe`・`native_decide`・`debug.skipKernelTC`（異常系テスト専用の分離箇所を除く）が残存している、または `check_shigure_declarations.lean` / `#shigure_assert_standard_axioms_only` が通らない。
3. 数学本文（第4–6章・付録B・設定 19.12・補題 19.13）の番号付き証明付き主張 25 件、節内主張（4.5 節の局所分裂複製対象の Zariski descent、B.3 の一般スキーム fppf descent およびスタック上相対 Spec 拡張、5.4/6.1 節の宣言制限・係数変更可換性）、または番号付き具体例 9 件および本文中の無番号具体例・反例のいずれかに未証明・省略・仮定追加（未放電仮定）・結論弱化・対象縮小（有限化・固定化・非零環への無断限定等）がある。
4. スキーム論の標準事実（平坦局所有限表示射の開性、滑らかな射の平坦性・基底変換安定性・fppf 局所性等）を未放電仮定・typeclass 仮定・構造フィールドへ逃がして閉じている。
5. 定義側に結論を埋め込む definitional escape、または mathlib の圏・余代数・多項式環・対称代数・加群・平坦性・スキーム・接着構成と接続しない閉じたラッパーで済ませている。
6. PRD 完了前に、本 PRD への参照がリポジトリ内の他文書・コードに残っている、または恒久規律の更新漏れがある。

---

## 6. 対象外（Non-Goals）

- **問題 6.11（一般の実現族の表示条件）**：数学本文で将来の研究課題として明記されているため本 PRD の対象外とする（問題 6.11(2) で触れられる Zariski 局所分裂対象の fppf 非閉性の注記自体は、必要に応じて AC-04 の補助反例として加えてよいが、問題 6.11 の一般条件決定は対象外とする）。
- **定理 19.14・定理 19.15（有限ハンケル表からの一意同型と復元）および第6.6節末尾の注（付録 D.5–D.6 のスペクトル根診断）**：第V部・第VI部で扱う範囲のため本 PRD の対象外とする（第 6.6 節の定理 6.12 に直接必要な設定 19.12 と補題 19.13 のみを本 PRD に含める）。
- 第III部以降（第7–19章の残り、付録 C–F）の形式化。
- 既存の `Formal/AG/`、`Formal/Util/`、`research/lean/`、ツール群（`tools/`）、公開面（`website/`）、および `.github/workflows/lean.yml` の改修。

---

## 7. 実装計画（推奨 PR 分割順）

1. **PR 1（AC-01）**：`Part2/AffineFoundations.lean`（補題 B.1, B.2, B.3）。
2. **PR 2（AC-02）**：`Part2/CopyingCoalgebra.lean`（定義 4.1, 構成 4.2, 定理 4.3, 例 4.4, 定義 4.5, 定理 4.6, 例 4.7）。
3. **PR 3（AC-03）**：`Part2/TensorRealizations.lean`（構成 4.8, 定理 4.9, 命題 4.10, 例 4.11）。
4. **PR 4（AC-04）**：`Part2/RealizationRecovery.lean`（定理 4.12, 局所充足例, 局所分裂複製対象の Zariski descent, 量スカラー読取り, 命題 4.13）。
5. **PR 5（AC-05）**：`Part2/QuantityModels.lean`（定義 5.1, 構成 5.2, 補題 5.3, 定理 5.4, 定理 5.5, 例 5.6, 例 5.7）。
6. **PR 6（AC-06）**：`Part2/QuantityTransport.lean`（定理 5.8, 命題 5.9, 例 5.10, 宣言制限と係数変更の可換性, 定理 5.11, 例 5.12）。
7. **PR 7（AC-07）**：`Part2/FaithfullyFlatDescent.lean`（補題 B.4, 補題 B.5）。
8. **PR 8（AC-08）**：`Part2/SchemesAndRelativeSpec.lean`（準連接加群/代数, 一般スキームの fppf descent, 補題 B.6, 補題 B.7, スタック上相対 Spec）。
9. **PR 9（AC-09）**：`Part2/RealizationStack.lean`（定義 6.1, 多項式 Law の展開と座標独立性, 補題 6.2）。
10. **PR 10（AC-10）**：`Part2/MarkedCharts.lean`（定義 6.3, 構成 6.4, 定理 6.5, 例 6.6）。
11. **PR 11（AC-11）**：`Part2/QuotientStack.lean`（代数的スタック・滑らかさ, 定理 6.7, 自己同型群スキーム, 階数直和, 例 6.8）。
12. **PR 12（AC-12）**：`Part2/StackRelativeSpec.lean`（定義 6.9, 定理 6.10, 残差計算例・非単射引戻し例・定理 5.4 の特殊場合）。
13. **PR 13（AC-13）**：`Part2/MinimalRealization.lean`（設定 19.12, 補題 19.13, 定理 6.12）。
14. **PR 14（AC-14）**：`Formal/SHIGURE.lean`・`Formal/SHIGURE/AxiomAudit.lean` の最終統合および全監査確認。

（AC-07・AC-08・AC-11・AC-12 のように実装規模が大きい AC は、依存順にサブ PR へ細分化して進めてよい。）

各 PR は [Workflow guideline](../workflow/guideline.md) の PR 前チェックおよび `math-lean-review`（独立 4 lane・別モデル PR レビュー）を通過してマージする。

---

## 8. 停止条件

次のいずれかに該当した時点で実装ループを停止し、状況を報告して人間判断を仰ぐ。

1. 数学本文（第4–6章・付録B・設定 19.12・補題 19.13）の記述に Lean 形式化上の曖昧さ・不整合・欠落が見つかり、Tier 1 文書の判断または PRD の改訂が必要になった場合（ループ内で PRD や数学本文を編集しない）。
2. [Lean 品質基準](../aat/lean_quality_standard.md) §5.3 に該当する target statement の変更（仮定の追加・結論の弱化・対象縮小）が必要と判明した場合。
3. mathlib v4.28.0 の欠落定理（例：平坦局所有限表示射の開性や滑らかさの一般論など）の自前証明が想定を大幅に超え、別 PRD への切り出しまたはツールチェーン更新の判断が必要になった場合。
4. 同一 AC で 2 周連続して PR がマージに至らない（`stalled`）場合。
5. 独立レビューゲート（`math-lean-review` / `$prd-completion-review`）が実行不能または `Blocked` となった場合。
