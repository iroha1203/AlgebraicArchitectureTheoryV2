# 共通記号

集合・写像・通常の代数・圏論を前提とする。小さい集合を扱う宇宙を固定し、
そのような集合全体の圏を扱う際には一つ大きい宇宙を用いる。
各担体、宣言の族、Lawの族は小さいものとする。有限性は式の長さと各操作のarityに課し、
族全体の有限性は必要な命題で指定する。空の担体も許す。
集合とその部分集合は外延的に、写像は点ごとの等号で比較する。

| 記号 | 意味 | 定義 |
| --- | --- | --- |
| $`\Sigma`$、$`S`$ | 署名とsortの集合 | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`\mathcal P`$、$`\mathbb T`$ | 名前付きの原始表示と、それが指定する理論 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射) |
| $`\mathrm{At}_{\mathrm{dec}}(\mathcal P)`$、$`\mathrm{At}_{\mathrm{val}}(A)`$ | 宣言と式の出現のAtom、評価された事実のAtom | [1.1](part_1/chapter_1_atoms_laws_theories.md#11-共通のatom語彙と個々のatom) |
| $`\Gamma=(x_i:s_i)_{i=1}^n`$ | 有限の変数文脈 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`X_s(A)`$ | 構造のsort担体 | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`X_\Gamma(A)`$ | 変数文脈に対応する担体の積 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`D_p^A`$、$`G_p^A`$ | 部分操作の定義域とgraph | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`\mathrm{Def}_t`$、$`E_t(\boldsymbol x,y)`$ | termの定義可能性と値を表す正の式 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\mathrm{ev}_A(t,\gamma)`$ | 入力 $`\gamma`$ でのtermの部分評価 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`I_\ell^A`$、$`J_\ell^A`$、$`\rho_{\ell,A}`$ | Lawの入力集合、両辺を評価できる入力、環値残差 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\theta`$、$`D_{\theta,A}`$、$`\theta_A`$ | termの代入、その全成分を評価できる入力と評価写像 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射) |
| $`\mathbf{Th}`$ | 理論と、相互導出で同一視した理論解釈の圏 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射)、[付録A](appendix_a_positive_logic.md#a3-翻訳と導出) |
| $`\mathrm{Str}_\Sigma`$、$`\mathcal A_{\mathbb T}`$ | 構造の圏と必須Lawを満たす意味圏 | [2.1–2.2](part_1/chapter_2_models_and_morphisms.md#21-状態操作関係を持つ構造) |
| $`\mathcal A_{\mathbb T;M_0}`$ | 部分署名の解釈を固定し、そのsortの射を恒等とした意味圏 | [2.2](part_1/chapter_2_models_and_morphisms.md#22-lawを満たすモデルと観測) |
| $`u:\mathbb T\to\mathbb T'`$、$`u^*`$ | 理論解釈と反対向きのモデル引戻し | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`\mathcal A_{\mathrm{tot}}`$ | 理論とモデルをともに動かす全体圏 | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`o_A:X_s(A)\to O`$ | 指定sortの状態の観測 | [1.5](part_1/chapter_1_atoms_laws_theories.md#15-観測とreading) |
| $`\mathbf{Lens}`$、$`\mathbf{Prot}(\mathcal E,O)`$ | 全域lensの圏、実行圏と観測を固定したprotocolの圏 | [2.5](part_1/chapter_2_models_and_morphisms.md#25-独立な意味論からの構成と回復) |
| $`U`$、$`\mathcal A(U)`$、$`A\vert_U`$ | 宣言文脈、そのモデル圏、制限 | [3.1–3.2](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Ctx}(\mathcal P)`$ | 宣言文脈と包含の圏 | [3.1](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Supp}(t)`$、$`\mathrm{Supp}(\varphi)`$、$`\mathrm{Supp}(\ell)`$ | term・式・Lawを入力文脈とともに読むための宣言の支持 | [3.1](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Match}((U_i),\mathcal A)`$ | 宣言被覆上の厳密な整合局所モデルと整合局所射の圏 | [3.3](part_1/chapter_3_contexts_and_local_models.md#33-被覆と局所整合データ) |
| $`K_s`$、$`Q_s=R^{m_s}/K_s`$ | 生成元付き加群のkernelと商加群 | [3.3](part_1/chapter_3_contexts_and_local_models.md#生成元付き加群への適用) |
| $`k`$、$`R`$、$`\sigma`$ | 基礎環、係数となる可換代数、係数的実現方式 | [4.1](part_2/chapter_4_coefficient_realizations.md#41-原始実現データと係数に沿う関手) |
| $`\mathcal A_{\mathbb T,\sigma}(U,R)`$ | 宣言文脈と係数を指定した実現の意味圏 | [4.1](part_2/chapter_4_coefficient_realizations.md#41-原始実現データと係数に沿う関手) |
| $`C_R(X)`$、$`\underline X_R`$ | copying coalgebraと、集合の状態を保持するschemeの族 | [4.2](part_2/chapter_4_coefficient_realizations.md#42-複製消去を保つcoalgebra) |
| $`F=(F_x)`$、$`P_F`$ | 入力ごとの有限supportとその係数のchart | [4.3](part_2/chapter_4_coefficient_realizations.md#43-無限担体とtotality) |
| $`M_R=M\otimes_kR`$、$`\iota_{M,R}`$ | 加群のtensor実現とcopyingからの比較写像 | [4.4](part_2/chapter_4_coefficient_realizations.md#44-加群のtensor実現と比較) |
| $`S`$、$`D_j(S)`$、$`E_\ell(S)`$ | 固定構造、量domain、固定したLaw入力。ここでの $`S`$ はsort集合と別の記号 | [5.1](part_2/chapter_5_quantities_and_law_geometry.md#51-固定構造上の量モデル) |
| $`\mathrm{QMod}_S(R)`$ | 関数と原式の充足から定義する量・Lawモデル | [5.1](part_2/chapter_5_quantities_and_law_geometry.md#51-固定構造上の量モデル) |
| $`Q_S`$、$`A_S`$、$`\rho_\ell`$、$`I_S`$ | 量座標の自由加群、多項式環、普遍残差、残差生成イデアル | [5.2](part_2/chapter_5_quantities_and_law_geometry.md#52-普遍量残差生成イデアル) |
| $`X_S`$、$`M_S`$ | 量のambientとLawful locus | [5.2–5.3](part_2/chapter_5_quantities_and_law_geometry.md#53-表現と通常のaffine幾何の回復) |
| $`\phi_h`$、$`M(h)`$、$`Z_h`$ | 構造射に沿う座標環射、量モデルの引戻し、量の一致の対応空間 | [5.4](part_2/chapter_5_quantities_and_law_geometry.md#54-構造射と量の引戻し) |
| $`E_F`$、$`E=\mathop{\mathrm{colim}}_F E_F`$ | 有限単項式supportごとの拡張と全拡張の関手 | [5.5](part_2/chapter_5_quantities_and_law_geometry.md#55-residualの係数拡張) |
| $`\mathcal M`$、$`\mathrm{Real}_{\boldsymbol n}`$ | 実現の同型groupoidの族、有限局所自由の階数別の族 | [6.1](part_2/chapter_6_families_and_moduli.md#61-係数実現の族と同型) |
| $`E_s`$、$`\pi_s`$、$`\mathrm{Mark}_{\boldsymbol m,\boldsymbol n}`$ | 加群層、名前付き生成元からの全射、生成元付き実現の同型類 | [6.2](part_2/chapter_6_families_and_moduli.md#62-生成元と基底chart) |
| $`U_I`$、$`M_{\boldsymbol m,\boldsymbol n}`$ | 選択生成元が基底となるchartと、その接着scheme | [6.2–6.3](part_2/chapter_6_families_and_moduli.md#63-chartの接着と普遍実現) |
| $`X_{\boldsymbol n}`$、$`G_{\boldsymbol n}`$、$`P_E`$ | 基底付きの演算係数scheme、基底変更群、frame torsor | [6.4](part_2/chapter_6_families_and_moduli.md#64-frame自己同型商stack) |
| $`\mathcal B_\sigma`$、$`Q`$、$`I`$、$`\mathcal C`$、$`\mathcal L`$ | 量を加える前の構造stack、量の型の加群、flat-fppf site上のLaw ideal、商代数、量・Lawモデルの相対Spec | [6.5](part_2/chapter_6_families_and_moduli.md#65-相対specと表示の成立条件) |

合成は $`(g\circ f)(x)=g(f(x))`$ の順で書く。
$`u:\mathbb T\to\mathbb T'`$ のモデル引戻しは
$`u^*:\mathcal A_{\mathbb T'}\to\mathcal A_{\mathbb T}`$ である。
宣言の包含 $`V\subseteq W`$ のモデル制限も $`\mathcal A(W)\to\mathcal A(V)`$ とする。
$`\Gamma`$ は変数文脈、$`U,V,W`$ は宣言文脈を表す。
幾何の節で用いる $`\Gamma(\Omega,\mathcal O)`$ は、開集合 $`\Omega`$ 上の切断の集合である。
基準viewによる積表示 $`\theta_L`$ は、term代入 $`\theta`$ と添字・定義域によって区別する。

係数を指定する際には、基礎環を $`k`$、$`k`$ 代数を $`R`$、
係数的実現方式を $`\sigma`$ と書く。後続の診断係数は $`\Lambda`$ とする。
原始表示 $`\mathcal P`$、固定部分 $`K_{\mathrm{fix}}`$、評価対象 $`E`$ は別の記号とする。
一つのモデルの状態、モデルを動かすパラメータ、モデル間の変更は、それぞれの担体で扱う。

第6章の有限sort集合は $`S_0`$、試験schemeは $`T`$、例の単項演算は $`N`$ と書く。
添字付きの $`E_s`$ は担体加群、$`E_\ell(S)`$ はLaw入力、$`E_F`$ は残差の拡張を表すschemeである。
$`J`$ は第5章では量の添字集合、第6章の $`I,J,K`$ は選択基底のchart添字である。
$`J_I`$ はそのchartのLaw ideal、$`K_s`$ はmarkingのkernelまたは、基底変更の式では選択列の添字を表す。
$`Q_s`$ は生成元付きの商担体、$`Q_S,Q_b,Q`$ は量の型を表す加群である。
第4章の $`K_x`$ は合成射の有限supportであり、いずれも定義域と添字で区別する。
第6章の $`I_b`$ は任意の試験射での像イデアルであり、加群の引戻し $`b^*I`$ と区別する。
