# 共通記号

集合・写像・通常の代数・圏論を前提とする。小さい集合を扱う宇宙を固定し、
そのような集合全体の圏を扱う際には一つ大きい宇宙を用いる。
各担体、宣言の族、Lawの族は小さいものとする。有限性は式の長さと各操作のarityに課し、
族全体の有限性は必要な命題で指定する。空の担体も許す。
集合とその部分集合は外延的に、写像は点ごとの等号で比較する。
基礎は選択公理を含む通常の集合論とする。担体の代表、自由生成元のlift、基底の選択にこれを用いる。
可算塔での再帰的持上げと積の完全性には可算の従属選択が十分であり、
有限集合の逆極限では第13章でBoolean prime ideal theoremによるコンパクト性を明記する。
これらは構成的な有限計算の主張とは区別する。
局所的な記号は、各設定・定理・例で指定した範囲で用いる。第11章の $`p,q`$ は塔の関手、
$`\pi_i,\pi_{\mathrm{ob}}`$ は線形商写像、$`B_i`$ は頂点補正空間、$`B_i^{\mathrm{par}}`$ はparameterの係数行列である。
同章で $`S\subseteq T`$ と書く $`T`$ は許可範囲、参照変更 $`h\mapsto h-a`$ の $`a`$ は基準の差を表す。
領域 $`U,V,W`$、評価条件 $`V\subseteq E`$、parameter集合 $`\mathsf V`$ は、それぞれの設定で区別する。
具体例の頂点名 $`p`$ は、その例で宣言した頂点を指す。

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
| $`\widehat{\mathcal C}_H`$、$`\mathcal B^{\partial}_{a,H}`$ | 元の記録と同型で運んだ変更を持つ表示、選んだ端点と $`a`$ の同定を保持するfiber | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`E`$、$`\widetilde v`$、$`V\hookrightarrow E`$、$`\mathcal F^{\partial}_{a,H,V}`$ | 評価関手、固定同定も読む評価、評価条件、$`\partial=s,t`$ で始域または終域を固定する条件付き変更族 | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`J`$、$`K_{\mathrm{fix}}`$、$`d`$、$`\alpha`$ | 図式形、固定部分圏、固定図式、そのtrivialization | [8.3](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式とtrivializationを保つ全補完) |
| $`\mathcal D_{J,K_{\mathrm{fix}},d}`$、$`\mathrm{Path}_{H,n}`$ | 固定図式の全補完、許された一段変更の経路 | [8.3–8.4](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式とtrivializationを保つ全補完) |
| $`\mathrm{Tr}(h,D)`$、$`m`$ | 指定domainからの全移送、$`hm=\iota_D`$ を満たす移送 | [8.5](part_3/chapter_8_constrained_changes_and_completions.md#85-状態移送と操作domainのlift) |
| $`\mathrm{Con}(S,T)`$、$`\mathscr R`$、$`\equiv_{\mathscr R}`$、$`\approx_o`$ | 操作合同関係の束、同一視要求、生成合同関係、全操作語の観測同値 | [9.1](part_3/chapter_9_quotients_symmetry_and_lifts.md#91-操作合同関係と観測同値) |
| $`q,s,N`$ | 操作・観測を保つ商、保存section、保存冪等射 $`N=sq`$ | [9.3](part_3/chapter_9_quotients_symmetry_and_lifts.md#93-保存section冪等射分裂) |
| $`\mathrm{Hol}_j`$、$`\mathrm{Lift}(g)`$、$`K`$ | 根のholonomy群、可視変更の全lift、垂直変更群 | [9.4](part_3/chapter_9_quotients_symmetry_and_lifts.md#94-holonomyと中心化群) |
| $`G_{\mathrm{chg}}\to G_{\mathrm{vis}}`$、$`G_{\mathrm{lift}}`$ | 全変更群の可視群への射影、その像 | [9.5](part_3/chapter_9_quotients_symmetry_and_lifts.md#95-持ち上げのfiberと選択の整合) |
| $`\mathrm{Desc}`$、$`\theta_{ij},\eta_{ab},\Xi`$ | descent圏、文脈・係数の同定、二方向の交換同型 | [10.1–10.3](part_4/chapter_10_descent_of_realizations_and_changes.md#101-文脈係数それぞれのdescent) |
| $`K,P=K_{\mathrm{fix}},E_0,\mathsf E,S`$ | 型付きセル表示、固定部分、常時許容辺、候補辺、許可範囲 | [11.1–11.2](part_4/chapter_11_ariadne_relative_repairs.md#111-原始実操作全核固定部分) |
| $`A_v,\rho_e,\delta,d^0,d^1,d^2`$ | 実射影の全核、実核輸送、実defect、セルの微分 | [11.1](part_4/chapter_11_ariadne_relative_repairs.md#111-原始実操作全核固定部分) |
| $`C_S^\bullet,\mathscr R_S(K),\Omega,\omega`$ | 範囲付き相対複体、実修復groupoid、局所案の統合障害の群と指定類 | [11.2–11.3](part_4/chapter_11_ariadne_relative_repairs.md#112-範囲付き実修復とコホモロジー分類) |
| $`\mathcal I_i,R_i,N_i,s_i,\mathrm{Glue}_S`$ | 一度生成する局所表現、公開関係、内部kernel、復元section、厳密合成 | [11.4](part_4/chapter_11_ariadne_relative_repairs.md#114-全範囲に共通する局所生成と厳密な組立て) |
| $`\mathsf O,o,B_e,\mathsf R_S,\mathcal H_o`$ | 常時許容補正の余核、要求類、候補写像、許可範囲の像、双対証拠の支持族 | [11.5](part_4/chapter_11_ariadne_relative_repairs.md#115-可否不能証拠極小範囲) |
| $`C_U(S),\mathop{\mathrm{Pair}}\nolimits(A_w)`$ | 内部候補を消去した共有関係、分割で生じる可縮なgroupoid | [11.6–11.8](part_4/chapter_11_ariadne_relative_repairs.md#116-表示比較内部置換文脈同値) |
| $`R'\to R,M,L_{A/k},\mathrm{ob}`$ | 平方零拡大、その核、余接複体、固定データに相対的なlift障害 | [12.1–12.2](part_4/chapter_12_deformations_and_obstructions.md#121-変形対象と固定データ) |
| $`M_{\mathrm{sem}},Q_E,\Phi,\beta`$ | repair wordの関係商、方程式の生成商 $`O_E/I_{\mathrm{Ob}}^E`$、係数同型、実状態と方程式liftの対応 | [12.4](part_4/chapter_12_deformations_and_obstructions.md#124-局所lift後の貼り合わせと意味比較) |
| $`B,I_1,I_2,\mathop{\mathrm{Tor}}\nolimits`$ | 共通ambient環、二つの残差イデアル、導来交差のコホモロジー | [12.5](part_4/chapter_12_deformations_and_obstructions.md#125-複数lawの導来交差とtor) |
| $`D_n,R\!\lim D_n,\lim^1`$ | 原始修正複体の塔、その導来逆極限、追加の整合障害を持つ導来関手 | [13.3](part_4/chapter_13_fragments_and_globalization.md#133-導来逆極限と追加障害) |
| $`B_b,\chi_{b,u}`$、$`e_!,e^*`$ | 係数変更と理論引戻しの比較、exactな原始対応に沿う輸送と逆向きの制限 | [14.1–14.3](part_5/chapter_14_transport_along_readings_and_coefficients.md#141-理論引戻しと係数実現readingatom観測) |
| $`L_u,R_u,\alpha:D\Rightarrow V`$ | 随伴を持つ輸送・制限、二経路を結ぶ生成mate | [15.1](part_5/chapter_15_generated_comparisons_and_normalization.md#151-二経路と標準比較) |
| $`\mathrm{Kar}(\mathcal E),(X,e),(Y,d),\beta`$ | 冪等射の像を対象とする圏、正規化された比較 | [15.2](part_5/chapter_15_generated_comparisons_and_normalization.md#152-冪等正規化と像) |
| $`r:G\to Q,\Gamma,\Delta,L`$ | 実比較の端点変更群から像の変更群への写像、適合部分群、制限準同型の核 | [15.4–15.5](part_5/chapter_15_generated_comparisons_and_normalization.md#154-保存反映持ち上げ) |
| $`S,q,\lambda_\ell,K_a,D_q,\Lambda`$ | 有限Source、reading、Law値readout、labelの可視セル、診断複体、診断係数 | [16.1](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#161-指定修復問題とlaw評価からの診断複体) |
| $`\mathrm{Cone}(F),J(f),\delta`$ | 比較の写像錐、次数1の核・余核の次元対、六項列の相殺写像 | [16.2](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#162-核余核写像錐と合成) |
| $`\Phi_c,\Gamma_e,\Psi_F,G,P,L_\bullet,\mathscr R,\tau`$ | セルlift、順像係数とその複体、退化部分複体、fiber適合空間と連結射 | [16.3](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#163-係数fiber局所貼り合わせによる分解) |
| $`Z_{\sigma,\ell},\mathscr D_B`$ | regular readoutの有限root scheme、定数étale層の順像から作る診断の族 | [16.4](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#164-実現族と値の合流)、[付録D](appendix_d_finite_roots_and_stalks.md) |
| $`M,g,[g],\mathrm{diag}(g)`$ | 原始関係商、実mismatch、指定実障害とその診断類 | [16.5](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#165-実障害の比較と零性反映) |
| $`D^\vee,\Delta_n,\mathcal H^n,h(g)`$ | 双対chain、Laplacian、harmonic空間、指定cocycleのharmonic射影 | [16.6](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#166-双対評価と有限hilbert複体による読取り) |

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

第11章の $`P`$ は固定部分であり、第12章の $`P=k[x_1,\ldots,x_n]`$ はambient多項式環である。
第11章の $`A_v`$ は実核の可換群、第12章の $`A`$ はchartの座標環である。
第11章の $`S\subseteq\mathsf E`$ は許可範囲、第13章の $`S_i`$ は解集合である。
第11章の $`R_i`$ は公開アフィン関係で、係数環 $`R`$ と区別する。
第12章の $`R_{\mathrm{rep}}(U)`$ はrepair wordの関係群である。
第13章の $`D_n`$ は複体であり、部分操作のdomainとは型で区別する。

第15章の $`\Gamma,\Delta`$ は適合する変更の部分群であり、変数文脈や第16章のLaplacian $`\Delta_n`$ とは別である。
第16章の $`S`$ はSource、$`L`$ はreadoutの有限添字集合、$`L_\bullet`$ は退化部分複体を表す。
同章16.3節の $`G`$ はセル係数系、$`P`$ はそのcochain複体、$`\Gamma_e`$ は辺liftの関係グラフ、
$`\mathscr R`$ はfiber類の適合部分空間である。16.5節の $`G`$ は実被覆のグラフ、
$`P=L\times S`$ は実係数の原始生成元集合であり、各節で型を指定し直す。
$`T`$ は16.1節ではreadingの値集合、16.3節では直接比較の $`H^1`$ 射である。
