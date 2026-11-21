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
| $`\mathbf T_\sigma`$、$`\boldsymbol U`$、$`\mathrm{Ctx}(\mathbf T_\sigma)`$ | 方式で許す理論と解釈、翻訳・導出の支持を保つ文脈族、その包含の圏 | [7.1](part_3/chapter_7_semantic_changes_and_composition.md#71-操作観測を保つ射) |
| $`\mathcal C`$、$`s,t`$、$`N_n`$ | 全意味保存射と可換な同型のgroupoid、始域・終域、合成可能な射のnerve | [7.3–7.4](part_3/chapter_7_semantic_changes_and_composition.md#73-全変更の関手と比較表示) |
| $`\mathcal P_{01,u}`$、$`H_s`$、$`\mathrm{Cmp}_\sigma`$ | 比較表示、状態写像の宣言、両端の対象条件と任意の許可写像を別に読む混合解釈のgroupoid | [7.3](part_3/chapter_7_semantic_changes_and_composition.md#73-全変更の関手と比較表示) |
| $`H`$、$`\mathrm{Syn}_H`$、$`\mathrm{Adm}_H=\mathcal C_H`$ | 型・適用域・解釈・比較を持つ許容規則、構文候補、独立な許容変更のgroupoid | [8.1–8.2](part_3/chapter_8_constrained_changes_and_completions.md#81-許容規則の構文意味同一視) |
| $`H_{\mathrm{poly}}`$、$`n_{v,s}`$ | 有限次数の多項式・行列を生成する規則、頂点とsortごとの階数 | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`\mathcal B^{\partial}_{a,H}`$ | 選んだ端点と $`a`$ の同定 $`\alpha`$ を保持するfiber | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`E`$、$`\widetilde v`$、$`V\hookrightarrow E`$、$`\mathcal F^{\partial}_{a,H,V}`$ | 評価関手、固定同定も読む評価、評価条件、$`\partial=s,t`$ で始域または終域を固定する条件付き変更族 | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`J`$、$`K_{\mathrm{fix}}`$、$`d`$、$`\alpha`$ | 図式形、固定部分圏、固定図式、そのtrivialization | [8.3](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式とtrivializationを保つ全補完) |
| $`\mathcal D_{J,K_{\mathrm{fix}},d}`$、$`\mathrm{Path}_{H,n}`$ | 固定図式の全補完、許された一段変更の経路 | [8.3–8.4](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式とtrivializationを保つ全補完) |
| $`\mathrm{Tr}(h,D)`$、$`m`$ | 指定domainからの全移送、$`hm=\iota_D`$ を満たす移送 | [8.5](part_3/chapter_8_constrained_changes_and_completions.md#85-状態移送と操作domainのlift) |
| $`\mathrm{Con}(S,T)`$、$`\mathscr R`$、$`\equiv_{\mathscr R}`$、$`\approx_o`$ | 操作合同関係の束、同一視要求、生成合同関係、全操作語の観測同値 | [9.1](part_3/chapter_9_quotients_symmetry_and_lifts.md#91-操作合同関係と観測同値) |
| $`q,s,N`$ | 操作・観測を保つ商、保存section、保存冪等射 $`N=sq`$ | [9.3](part_3/chapter_9_quotients_symmetry_and_lifts.md#93-保存section冪等射分裂) |
| $`\mathrm{Hol}_j`$、$`\mathrm{Lift}(g)`$、$`K`$ | 根のholonomy群、可視変更の全lift、垂直変更群 | [9.4](part_3/chapter_9_quotients_symmetry_and_lifts.md#94-holonomyと中心化群) |
| $`G_{\mathrm{chg}}\to G_{\mathrm{vis}}`$、$`G_{\mathrm{lift}}`$ | 全変更群の可視群への射影、その像 | [9.5](part_3/chapter_9_quotients_symmetry_and_lifts.md#95-持ち上げのfiberと選択の整合) |

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

第7章以降の変更groupoid $`\mathcal C`$ は、第6章の商代数 $`\mathcal C`$ と用途で区別する。
第8章の $`H`$ は許容規則、$`H_s`$ は比較表示の写像宣言である。
同章の $`V`$ は評価条件を表す部分関手であり、宣言文脈の包含に使う $`V`$ とは別である。
第9章では係数環 $`R`$ と同一視要求を区別するため、後者を $`\mathscr R`$ と書く。
商のsection $`s`$、全変更の始域関手 $`s`$、sort添字 $`s`$ は定義域で区別する。

第7–8章の $`D`$ は台帳の状態担体、第8章の $`D:J\to\mathcal A`$ は補完図式、
移送の $`D\hookrightarrow X_0`$ は移送domainであり、型で区別する。
$`E`$ は第8章では評価対象、第9章では名前付き操作の集合である。
第8章の $`J`$ は図式形、$`K_{\mathrm{fix}}`$ はその固定部分圏であり、
第9章の $`K`$ は垂直変更群である。
第9章の保存冪等射 $`N`$ と、第7章のnerve $`N_n`$ は添字と型で区別する。
第9章の $`r_j`$ は連結成分 $`j`$ の根、$`\omega_v`$ は頂点 $`v`$ の追加観測である。
中心化群 $`C_L(M)`$ の $`L,M`$ は群とその部分群を表す。
