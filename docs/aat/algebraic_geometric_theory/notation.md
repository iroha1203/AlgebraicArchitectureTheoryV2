# 共通記号

本書全体を通じて、集合・写像および通常の代数・圏論の標準的な事実を前提とする。基礎となる集合論と宇宙に関する規約は次のとおりである。

- 小さい集合を扱う宇宙を一つ固定し、小さい集合全体の圏を扱う際には一つ大きい宇宙を用いる。
- 各担体、宣言の族、および Law の族はいずれも小さい集合とする。有限性は式の長さと各操作の arity に課し、族全体の有限性が必要な場合には各命題の仮定で明示する。空の担体も許す。
- 集合とその部分集合は外延的に比較し、写像は点ごとの等号で比較する。
- 集合論の基礎には選択公理を含める。担体の代表元の選択、自由生成元の持ち上げ、および基底の選択にはこれを用いる。なお、可算塔における再帰的な持ち上げと積の完全性には可算の従属選択で十分であり、有限集合の逆極限では第13章で Boolean 素イデアル定理によるコンパクト性を明示する。これらの非構成的な原理は、構成的な有限計算の主張とは明確に区別する。

局所的な記号は、各設定・定理・例で指定された範囲において用いる。たとえば具体例の頂点名 $`p`$ は、その例の中で宣言された頂点を指す。以下では、まず第I–V部および第VI部の主要記号を一覧表にまとめ、その後に章ごとの記号の使い分けを整理する。

## 第I–V部の主要記号

| 記号 | 意味 | 定義 |
| --- | --- | --- |
| $`\Sigma`$、$`S`$ | 署名と sort の集合 | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`\mathcal P`$、$`\mathbb T`$ | 名前付きの原始表示と、それが指定する理論 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射) |
| $`\mathrm{At}_{\mathrm{dec}}(\mathcal P)`$、$`\mathrm{At}_{\mathrm{val}}(A)`$ | 宣言と式の出現の Atom、および評価された事実の Atom | [1.1](part_1/chapter_1_atoms_laws_theories.md#11-共通のatom語彙と個々のatom) |
| $`\Gamma=(x_i:s_i)_{i=1}^n`$ | 有限の変数文脈 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`X_s(A)`$ | 構造における sort の担体 | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`X_\Gamma(A)`$ | 変数文脈に対応する担体の直積 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`D_p^A`$、$`G_p^A`$ | 部分操作の定義域とグラフ | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`\mathrm{Def}_t`$、$`E_t(\boldsymbol x,y)`$ | 項の定義可能性と値を表す正の式 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\mathrm{ev}_A(t,\gamma)`$ | 入力 $`\gamma`$ における項の部分評価 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`I_\ell^A`$、$`J_\ell^A`$、$`\rho_{\ell,A}`$ | Law の入力集合、両辺を評価できる入力、および環値の残差 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\theta`$、$`D_{\theta,A}`$、$`\theta_A`$ | 項の代入、すべての成分を評価できる入力、およびその評価写像 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射) |
| $`\mathbf{Th}`$ | 理論と、相互導出によって同一視した理論解釈の圏 | [1.4](part_1/chapter_1_atoms_laws_theories.md#14-表示代入理論の射)、[付録A](appendix_a_positive_logic.md#a3-翻訳と導出) |
| $`\mathrm{Str}_\Sigma`$、$`\mathcal A_{\mathbb T}`$ | 構造の圏と、必須 Law を満たすモデルの意味圏 | [2.1–2.2](part_1/chapter_2_models_and_morphisms.md#21-状態操作関係を持つ構造) |
| $`\mathcal A_{\mathbb T;M_0}`$ | 部分署名の解釈を固定し、その sort の射を恒等にした意味圏 | [2.2](part_1/chapter_2_models_and_morphisms.md#22-lawを満たすモデルと観測) |
| $`u:\mathbb T\to\mathbb T'`$、$`u^*`$ | 理論解釈と、それに伴う反変のモデル引き戻し | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`\mathcal A_{\mathrm{tot}}`$ | 理論とモデルをともに動かす全体圏 | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`o_A:X_s(A)\to O`$ | 指定された sort の状態の観測 | [1.5](part_1/chapter_1_atoms_laws_theories.md#15-観測とreading) |
| $`\mathbf{Lens}`$、$`\mathbf{Prot}(\mathcal E,O)`$ | 全域 lens の圏、および実行圏と観測を固定した protocol の圏 | [2.5](part_1/chapter_2_models_and_morphisms.md#25-独立な意味論からの構成と回復) |
| $`U`$、$`\mathcal A(U)`$、$`A\vert_U`$ | 宣言文脈、そのモデル圏、および制限 | [3.1–3.2](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Ctx}(\mathcal P)`$ | 宣言文脈と包含射の圏 | [3.1](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Supp}(t)`$、$`\mathrm{Supp}(\varphi)`$、$`\mathrm{Supp}(\ell)`$ | 項・式・Law を入力文脈とともに読むための宣言の支持 | [3.1](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Match}((U_i),\mathcal A)`$ | 宣言被覆上の厳密に整合する局所モデルと局所射の圏 | [3.3](part_1/chapter_3_contexts_and_local_models.md#33-被覆と局所整合データ) |
| $`K_s`$、$`Q_s=R^{m_s}/K_s`$ | 生成元付き加群の核と商加群 | [3.3](part_1/chapter_3_contexts_and_local_models.md#生成元付き加群への適用) |
| $`k`$、$`R`$、$`\sigma`$ | 基礎環、係数となる可換代数、および係数的実現方式 | [4.1](part_2/chapter_4_coefficient_realizations.md#41-原始実現データと係数に沿う関手) |
| $`\mathcal A_{\mathbb T,\sigma}(U,R)`$ | 宣言文脈と係数を指定した実現の意味圏 | [4.1](part_2/chapter_4_coefficient_realizations.md#41-原始実現データと係数に沿う関手) |
| $`C_R(X)`$、$`\underline X_R`$ | 複製余代数と、集合の状態を保持するスキームの族 | [4.2](part_2/chapter_4_coefficient_realizations.md#42-複製消去を保つ余代数) |
| $`F=(F_x)`$、$`P_F`$ | 入力ごとの有限な台（サポート）と、その係数のチャート | [4.3](part_2/chapter_4_coefficient_realizations.md#43-無限担体と全域性) |
| $`M_R=M\otimes_kR`$、$`\iota_{M,R}`$ | 加群のテンソル実現と、複製余代数からの比較写像 | [4.4](part_2/chapter_4_coefficient_realizations.md#44-加群のテンソル実現と比較) |
| $`S`$、$`D_j(S)`$、$`E_\ell(S)`$ | 固定構造、量の定義域、および固定した Law 入力（ここでの $`S`$ は sort 集合とは別の記号） | [5.1](part_2/chapter_5_quantities_and_law_geometry.md#51-固定構造上の量モデル) |
| $`\mathrm{QMod}_S(R)`$ | 関数と元の式の充足から定義する量・Law モデル | [5.1](part_2/chapter_5_quantities_and_law_geometry.md#51-固定構造上の量モデル) |
| $`Q_S`$、$`A_S`$、$`\rho_\ell`$、$`I_S`$ | 量座標の自由加群、多項式環、普遍残差、および残差生成イデアル | [5.2](part_2/chapter_5_quantities_and_law_geometry.md#52-普遍量残差生成イデアル) |
| $`X_S`$、$`M_S`$ | 量の周囲空間と Lawful locus | [5.2–5.3](part_2/chapter_5_quantities_and_law_geometry.md#53-表現と通常のアフィン幾何の回復) |
| $`\phi_h`$、$`M(h)`$、$`Z_h`$ | 構造射に沿う座標環の射、量モデルの引き戻し、および量の一致の対応空間 | [5.4](part_2/chapter_5_quantities_and_law_geometry.md#54-構造射と量の引き戻し) |
| $`E_F`$、$`E=\mathop{\mathrm{colim}}_F E_F`$ | 有限単項式の台ごとの拡張と、すべての拡張の余極限関手 | [5.5](part_2/chapter_5_quantities_and_law_geometry.md#55-残差の係数拡張) |
| $`\mathcal M`$、$`\mathrm{Real}_{\boldsymbol n}`$ | 実現の同型 groupoid の族、および有限局所自由の階数別の族 | [6.1](part_2/chapter_6_families_and_moduli.md#61-係数実現の族と同型) |
| $`E_s`$、$`\pi_s`$、$`\mathrm{Mark}_{\boldsymbol m,\boldsymbol n}`$ | 加群層、名前付き生成元からの全射、および生成元付き実現の同型類 | [6.2](part_2/chapter_6_families_and_moduli.md#62-生成元と基底チャート) |
| $`U_I`$、$`M_{\boldsymbol m,\boldsymbol n}`$ | 選んだ生成元が基底となるチャートと、その接着スキーム | [6.2–6.3](part_2/chapter_6_families_and_moduli.md#63-チャートの接着と普遍実現) |
| $`X_{\boldsymbol n}`$、$`G_{\boldsymbol n}`$、$`P_E`$ | 基底付きの演算係数スキーム、基底変更群、およびフレーム torsor | [6.4](part_2/chapter_6_families_and_moduli.md#64-フレーム自己同型商スタック) |
| $`\mathcal B_\sigma`$、$`Q`$、$`I`$、$`\mathcal C`$、$`\mathcal L`$ | 量を加える前の構造スタック、量の型の加群、平坦 fppf site 上の Law イデアル、商代数、および量・Law モデルの相対 $`\mathrm{Spec}`$ | [6.5](part_2/chapter_6_families_and_moduli.md#65-相対specと表示の成立条件) |
| $`\mathbf T_\sigma`$、$`\boldsymbol U`$、$`\mathrm{Ctx}(\mathbf T_\sigma)`$ | 方式で許す理論と解釈、翻訳・導出の支持を保つ文脈族、およびその包含の圏 | [7.1](part_3/chapter_7_semantic_changes_and_composition.md#71-操作観測を保つ射) |
| $`\mathcal C`$、$`s,t`$、$`N_n`$ | すべての意味保存射と可換な同型がなす groupoid、始域・終域、および合成可能な射の nerve | [7.3–7.4](part_3/chapter_7_semantic_changes_and_composition.md#73-すべての変更からなる関手と比較表示) |
| $`\mathcal P_{01,u}`$、$`H_s`$、$`\mathrm{Cmp}_\sigma`$ | 比較表示、状態写像の宣言、および両端の対象条件と任意の許可写像を別に読む混合解釈の groupoid | [7.3](part_3/chapter_7_semantic_changes_and_composition.md#73-すべての変更からなる関手と比較表示) |
| $`H`$、$`\mathrm{Syn}_H`$、$`\mathrm{Adm}_H=\mathcal C_H`$ | 型・適用域・解釈・比較をもつ許容規則、構文候補、および独立に定義した許容変更の groupoid | [8.1–8.2](part_3/chapter_8_constrained_changes_and_completions.md#81-許容規則の構文意味同一視) |
| $`H_{\mathrm{poly}}`$、$`n_{v,s}`$ | 有限次数の多項式・行列を生成する規則、および頂点と sort ごとの階数 | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`\widehat{\mathcal C}_H`$、$`\mathcal B^{\partial}_{a,H}`$ | 元の記録と同型で運んだ変更をもつ表示、および選んだ端点と $`a`$ の同定を保持するファイバー | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`E`$、$`\widetilde v`$、$`V\hookrightarrow E`$、$`\mathcal F^{\partial}_{a,H,V}`$ | 評価関手、固定同定も読む評価、評価条件、および $`\partial=s,t`$ で始域または終域を固定する条件付き変更族 | [8.2](part_3/chapter_8_constrained_changes_and_completions.md#82-候補生成と条件付き変更族) |
| $`J`$、$`K_{\mathrm{fix}}`$、$`d`$、$`\alpha`$ | 図式形、固定部分圏、固定図式、およびその自明化 | [8.3](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式と自明化を保つ補完の全体) |
| $`\mathcal D_{J,K_{\mathrm{fix}},d}`$、$`\mathrm{Path}_{H,n}`$ | 固定図式の補完の全体、および許された一段階の変更の経路 | [8.3–8.4](part_3/chapter_8_constrained_changes_and_completions.md#83-固定図式と自明化を保つ補完の全体) |
| $`\mathrm{Tr}(h,D)`$、$`m`$ | 指定定義域からの移送の全体、および $`hm=\iota_D`$ を満たす移送 | [8.5](part_3/chapter_8_constrained_changes_and_completions.md#85-状態移送と操作の定義域の持ち上げ) |
| $`\mathrm{Con}(S,T)`$、$`\mathscr R`$、$`\equiv_{\mathscr R}`$、$`\approx_o`$ | 操作合同関係の束、同一視要求、生成合同関係、およびすべての操作語に関する観測同値 | [9.1](part_3/chapter_9_quotients_symmetry_and_lifts.md#91-操作合同関係と観測同値) |
| $`q,s,N`$ | 操作・観測を保つ商、保存切断、および保存冪等射 $`N=sq`$ | [9.3](part_3/chapter_9_quotients_symmetry_and_lifts.md#93-保存切断冪等射分裂) |
| $`\mathrm{Hol}_j`$、$`\mathrm{Lift}(g)`$、$`K`$ | 根の holonomy 群、可視変更のすべての持ち上げ、および垂直変更群 | [9.4](part_3/chapter_9_quotients_symmetry_and_lifts.md#94-holonomy-と中心化群) |
| $`G_{\mathrm{chg}}\to G_{\mathrm{vis}}`$、$`G_{\mathrm{lift}}`$ | 変更群全体から可視群への射影と、その像 | [9.5](part_3/chapter_9_quotients_symmetry_and_lifts.md#95-持ち上げのファイバーと選択の整合) |
| $`\mathrm{Desc}`$、$`\theta_{ij},\eta_{ab},\Xi`$ | descent 圏、文脈・係数の同定、および 2 方向の交換同型 | [10.1–10.3](part_4/chapter_10_descent_of_realizations_and_changes.md#101-文脈係数それぞれのdescent) |
| $`K,P=K_{\mathrm{fix}},E_0,\mathsf E,S`$ | 型付きセル表示、固定部分、常時許容辺、候補辺、および許可範囲 | [11.1–11.2](part_4/chapter_11_ariadne_relative_repairs.md#111-原始的な操作射影の核固定部分) |
| $`A_v,\rho_e,\delta,d^0,d^1,d^2`$ | ファイバー自己同型の射影の核、核輸送、実際の欠陥（defect）、およびセルの微分 | [11.1](part_4/chapter_11_ariadne_relative_repairs.md#111-原始的な操作射影の核固定部分) |
| $`C_S^\bullet,\mathscr R_S(K),\Omega,\omega`$ | 範囲付き相対複体、修復の groupoid、および局所案の統合障害の群と指定類 | [11.2–11.3](part_4/chapter_11_ariadne_relative_repairs.md#112-範囲付き修復とコホモロジー分類) |
| $`\mathcal I_i,R_i,N_i,s_i,\mathrm{Glue}_S`$ | 一度生成する局所表現、公開関係、内部の核、復元切断、および厳密な合成 | [11.4](part_4/chapter_11_ariadne_relative_repairs.md#114-すべての許可範囲に共通する局所生成と厳密な組立て) |
| $`\mathsf O,o,B_e,\mathsf R_S,\mathcal H_o`$ | 常時許容補正の余核、要求類、候補写像、許可範囲の像、および双対証拠の支持族 | [11.5](part_4/chapter_11_ariadne_relative_repairs.md#115-可否不能証拠極小範囲) |
| $`C_U(S),\mathop{\mathrm{Pair}}\nolimits(A_w)`$ | 内部候補を消去した共有関係、および分割によって生じる可縮な groupoid | [11.6–11.8](part_4/chapter_11_ariadne_relative_repairs.md#116-表示比較内部置換文脈同値) |
| $`R'\to R,M,L_{A/k},\mathrm{ob}`$ | 平方零拡大、その核、余接複体、および固定データに相対的な持ち上げの障害 | [12.1–12.2](part_4/chapter_12_deformations_and_obstructions.md#121-変形対象と固定データ) |
| $`M_{\mathrm{sem}},Q_E,\Phi,\beta`$ | 修復語の関係商、方程式の生成商 $`O_E/I_{\mathrm{Ob}}^E`$、係数同型、および具体的な状態と方程式の持ち上げの対応 | [12.4](part_4/chapter_12_deformations_and_obstructions.md#124-局所的な持ち上げの貼り合わせと意味比較) |
| $`B,I_1,I_2,\mathop{\mathrm{Tor}}\nolimits`$ | 共通の周囲環、二つの残差イデアル、および導来交差のコホモロジー | [12.5](part_4/chapter_12_deformations_and_obstructions.md#125-複数lawの導来交差とtor) |
| $`D_n,R\!\lim D_n,\lim^1`$ | 原始修正複体の塔、その導来逆極限、および追加の整合障害をもつ導来関手 | [13.3](part_4/chapter_13_fragments_and_globalization.md#133-導来逆極限と追加障害) |
| $`B_b,\chi_{b,u}`$、$`e_!,e^*`$ | 係数変更と理論引き戻しの比較、および完全な原始対応に沿う輸送と逆向きの制限 | [14.1–14.3](part_5/chapter_14_transport_along_readings_and_coefficients.md#141-理論引き戻しと係数実現readingatom-観測) |
| $`L_u,R_u,\alpha:D\Rightarrow V`$ | 随伴をもつ輸送・制限、および 2 本の経路を結ぶ生成 mate | [15.1](part_5/chapter_15_generated_comparisons_and_normalization.md#151-2本の経路と標準比較) |
| $`\mathrm{Kar}(\mathcal E),(X,e),(Y,d),\beta`$ | 冪等射の像を対象とする圏と、正規化された比較 | [15.2](part_5/chapter_15_generated_comparisons_and_normalization.md#152-冪等正規化と像) |
| $`r:G\to Q,\Gamma,\Delta,L`$ | 具体的な比較の端点変更群から像の変更群への写像、適合部分群、および制限準同型の核 | [15.4–15.5](part_5/chapter_15_generated_comparisons_and_normalization.md#154-保存反映持ち上げ) |
| $`S,q,\lambda_\ell,K_a,D_q,\Lambda`$ | 有限 Source、reading、Law 値の読み出し、ラベルの可視セル、診断複体、および診断係数 | [16.1](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#161-指定修復問題と-law-評価からの診断複体) |
| $`\mathrm{Cone}(F),J(f),\delta`$ | 比較の写像錐、次数 1 の核・余核の次元対、および六項列の相殺写像 | [16.2](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#162-核余核写像錐と合成) |
| $`\Phi_c,\Gamma_e,\Psi_F,G,P,L_\bullet,\mathscr R,\tau`$ | セルの持ち上げ、順像係数とその複体、退化部分複体、およびファイバー適合空間と連結射 | [16.3](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#163-係数ファイバー局所貼り合わせによる分解) |
| $`Z_{\sigma,\ell},\mathscr D_B,\mathscr D_{\mathrm{sp}}`$ | 支持ごとの有限根スキームと、定数 étale 層の順像から作る診断の族。スカラー読み出しによる $`\mathscr D_B`$ は、原始自己準同型の特性多項式による $`\mathscr D_{\mathrm{sp}}`$ の階数1の場合 | [16.4](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#164-実現族と値の合流)、構成16.31・定理16.32、[付録DのD.5–D.6節](appendix_d_finite_roots_and_stalks.md#d5-一般のモニック多項式とスペクトル根) |
| $`M,g,[g],\mathrm{diag}(g)`$ | 原始関係商、実際の不一致、および指定された実際の障害とその診断類 | [16.5](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#165-実際の障害の比較と零性反映) |
| $`D^\vee,\Delta_n,\mathcal H^n,h(g)`$ | 双対チェイン、Laplacian、調和空間、および指定コサイクルの調和射影 | [16.6](part_5/chapter_16_diagnostic_families_and_obstruction_comparison.md#166-双対評価と有限-hilbert-複体による読取り) |

## 観測・修復・再構成の記号

第17–19章では、入力となる実現族を $`\mathcal U`$、宣言文脈を $`U`$ と書き分ける。また、$`s`$ は既知情報の値、$`\partial=s,t`$ は変更の固定端点の指定を表し、型と使用箇所によって区別する。

| 記号 | 意味 | 定義 |
| --- | --- | --- |
| $`\mathcal X_s\to\mathcal U,\ w_j,s_j,\ q:\mathcal U\to B`$ | 状態を印としてもつ族、評価語と切断、および実現族の観測 | [17.1](part_6/chapter_17_observation_sufficiency_and_selection.md#171-状態観測law-の読み出しから実現族の観測へ) |
| $`\eta,s,U_s,U_{s,b}`$ | 既知情報、その値、入力の制限、および観測ファイバー | [17.2](part_6/chapter_17_observation_sufficiency_and_selection.md#172-既知情報観測ファイバーと出力十分性) |
| $`p:\mathcal F\to\mathcal U,\ C_b,\mathrm{Valid}(u,c)`$ | すべての変更元にわたる解の族、共通候補の型、および有効性の関係 | [17.2–17.3](part_6/chapter_17_observation_sufficiency_and_selection.md#173-共通候補と解の選択) |
| $`a(\tau),E(\tau),V(\tau),T_\tau,\beta_{\tau,c}`$ | 入力射の実現、評価先と合格値の輸送、および可変規則の記録輸送と端点比較 | [17.2 構成17.5](part_6/chapter_17_observation_sufficiency_and_selection.md#172-既知情報観測ファイバーと出力十分性) |
| $`G_{(J)},R_T,R_V,F_{R,A}`$ | 観測点の安定化群、値とチャートの分割、および粗視化の診断比較 | [17.4–17.5](part_6/chapter_17_observation_sufficiency_and_selection.md#175-安全な解像度と選択の三つの問題) |
| $`P_S,P_{\mathrm{in}},Y,D_S,B_{\mathrm{in}},b_0`$ | 補正空間、未知入力空間、欠陥の空間、および同じ修復問題から生成する補正式 | [18.1](part_6/chapter_18_repair_and_observation.md#181-実際の操作からの補正方程式) |
| $`\pi_S,o_S,A_S`$ | 補正像で割る商写像、指定された残存障害、および入力方向の障害写像 | [18.2](part_6/chapter_18_repair_and_observation.md#182-残存障害と双対観測) |
| $`L,F_s,N,O_J,\lambda_j,m_C`$ | 線形な既知情報、そのファイバーと核、問い合わせ評価、および最適追加問い合わせ数 | [18.3–18.4](part_6/chapter_18_repair_and_observation.md#183-既知情報を条件とする十分性) |
| $`\Lambda_X,\mathcal L_{\mathbb T},N,\mathsf{Asm}`$ | 原始項目、整合する局所表の圏、読み取り関手、および組み立て関手 | [19.1–19.2](part_6/chapter_19_local_reconstruction_and_finite_determination.md#191-原始読み取りと局所モデル) |
| $`\mathcal L_{\mathbb T,\sigma}(R),N_\sigma,\mathsf{Asm}_\sigma`$ | 係数方式ごとの局所表、および対象とすべての射の読み取り関手・組み立て関手 | [19.2](part_6/chapter_19_local_reconstruction_and_finite_determination.md#192-対象と射の組み立て) |
| $`\mathcal F^{\mathrm{loc}},N_H,\mathsf{Asm}_H`$ | 局所的な解の全体族、および許容記録の読み取りと復元 | [19.3](part_6/chapter_19_local_reconstruction_and_finite_determination.md#193-条件付き変更と修復全体の相対再構成) |
| $`F,j:\pi_0(G[F])\to\pi_0(G)`$ | 有限頂点の読み取り、および誘導部分グラフから全体への連結成分写像 | [19.4](part_6/chapter_19_local_reconstruction_and_finite_determination.md#194-有限決定と実行可能な復元) |
| $`A,\mathfrak m_a,J,B,r`$ | 基点の局所環、極大イデアル、消去後の残差イデアル、次数上界、および Artin 試験次数 | [19.5](part_6/chapter_19_local_reconstruction_and_finite_determination.md#195-すべての有限断片有限次数試験と大域的回復) |

## 指定修復・必要情報・有限語再構成の記号

| 記号 | 意味 | 定義と計算 |
| --- | --- | --- |
| $`F_S:C_S^\bullet\to C_S'^\bullet`$ | 原始操作の比較から生成する範囲付き複体の写像 | 構成11.20、定理11.21–11.22 |
| $`\mathrm{Cone}(F)^n=D^n\oplus C^{n+1}`$ | 微分 $`(y,x)\mapsto(d_Dy+Fx,-d_Cx)`$ を持つ写像錐 | 16.2節、定理16.20 |
| $`G=\mathop{\mathrm{im}}\nolimits d^0,\ Z=\ker d^1,\ U=C_S^1`$ | 全許可範囲の再同定像・閉補正と、許可された辺の座標 | 定理11.23・18.17 |
| $`Q_c,Q_f,q,Z`$ | 二領域の交差の零次余核とその比較、および一次比較で失われる交差の像 | 定理16.25。この $`Z`$ は閉補正の群とは別に定義する |
| $`\mathcal N=\mathcal I/\mathcal I^2,\ \partial_{\mathcal U}(s)`$ | Law 生成余法係数と、指定切断の一次持ち上げ障害 | 定理12.13 |
| $`T=\mathop{\mathrm{Spec}}\nolimits A,\ K_t=\kappa(t)`$ | 既知の構造パラメータの空間と、各点の剰余体 | 設定18.11 |
| $`Q_J=(L,O_J),\ m_{\mathrm{dec}},m_{\mathrm{num}}`$ | 既知情報と問い合わせの行列、判定と数値補正の最適問い合わせ数 | 定理18.12・18.15。$`Q_J`$ は縦の並置 |
| $`P_{s,r},Q_{s,r},R_{s,r},O_{s,r}`$ | 長さ $`r`$ 以下の入力語・出力語の加群と、到達・観測写像 | 設定19.12 |
| $`N=\sum_s n_s,\ H_s,H_e`$ | 総階数、有限ハンケル写像、1操作を挿入したハンケル写像 | 定理19.14–19.15 |
| $`M_{\boldsymbol n}^{\min}`$ | 到達と双対観測が全射な最小実現のモジュライ | 定理6.12 |
| $`g_n=\det'((d^{n-1})^\top d^{n-1})`$ | 指定整数基底から作るねじれ消去整数・有理解の分母上界 | 補題C.4・定理C.5。非零固有値の空積は1 |
| $`R_n,t_n,\nu_n`$ | 調和レギュレータ、整数コホモロジーのねじれの位数、整数格子の共体積 | 定理C.7 |

ここで実現の係数環 $`k`$ と診断の係数環 $`\Lambda`$ は別々に指定する。整数基底に関する転置 $`(-)^\top`$ と、選んだ内積に関する随伴 $`(-)^*`$ も区別する。観測範囲の有限幅、公開語の長さ、問い合わせ集合の濃度は異なる量である。

## 記法の規約と章ごとの記号の使い分け

本書全体で、写像の合成は $`(g\circ f)(x)=g(f(x))`$ の順で書く。理論解釈 $`u:\mathbb T\to\mathbb T'`$ に対するモデルの引き戻しは $`u^*:\mathcal A_{\mathbb T'}\to\mathcal A_{\mathbb T}`$ とし、宣言文脈の包含 $`V\subseteq W`$ に対するモデルの制限も同様に反変の関手 $`\mathcal A(W)\to\mathcal A(V)`$ と書く。

係数を指定する際には、基礎環を $`k`$、$`k`$-代数を $`R`$、係数的実現方式を $`\sigma`$ とし、第V部の診断係数は $`\Lambda`$ と書く。原始表示 $`\mathcal P`$、固定部分 $`K_{\mathrm{fix}}`$、評価対象 $`E`$ は互いに別の記号とする。また、一つのモデルの状態、モデルを動かすパラメータ、およびモデル間の変更は、それぞれ別の担体で扱う。

複数の章で同じ文字を用いる記号については、以下のように定義域・添字・文脈によって明確に区別する。

- **文脈と切断（第I–VI部共通）**：$`\Gamma`$ は変数文脈、$`U,V,W`$ は宣言文脈を表す。幾何の節で現れる $`\Gamma(\Omega,\mathcal O)`$ は開集合 $`\Omega`$ 上の切断の集合である。基準 view による積表示 $`\theta_L`$ は、項の代入 $`\theta`$ と添字および定義域で区別する。また、領域 $`U,V,W`$、評価条件 $`V\subseteq E`$、パラメータ集合 $`\mathsf V`$ はそれぞれの設定で区別する。
- **第4–6章（係数的実現・量・モジュライ）**：
  - 第6章では有限 sort 集合を $`S_0`$、試験スキームを $`T`$、具体例の単項演算を $`N`$ と書く。
  - 添字付きの $`E_s`$ は担体加群、$`E_\ell(S)`$ は Law 入力、$`E_F`$ は残差の拡張を表すスキームである。
  - $`J`$ は第5章では量の添字集合を、第6章の $`I,J,K`$ は選択基底のチャート添字を表す。$`J_I`$ はそのチャートの Law イデアル、$`K_s`$ はマーキングの核（または基底変更の式では選択列の添字）を表す。
  - $`Q_s`$ は生成元付きの商担体、$`Q_S,Q_b,Q`$ は量の型を表す加群である。第4章の $`K_x`$ は合成射の有限な台であり、いずれも定義域と添字で区別する。
  - 第6章の $`I_b`$ は任意の試験射のもとでの像イデアルであり、加群の引き戻し $`b^*I`$ と区別する。
- **第7–9章（意味保存変更・補完・商と持ち上げ）**：
  - 第7章以降の変更 groupoid $`\mathcal C`$ は、第6章の商代数 $`\mathcal C`$ と用途で区別する。
  - 第8章の $`H`$ は許容規則、$`H_s`$ は比較表示における写像宣言である。同章の $`V`$ は評価条件を表す部分関手であり、宣言文脈の $`V`$ とは別である。また、第7–8章の $`D`$ は台帳の状態担体、第8章の $`D:J\to\mathcal A`$ は補完図式、移送の $`D\hookrightarrow X_0`$ は移送の定義域であり、型で区別する。
  - 第9章では係数環 $`R`$ と同一視要求を区別するため、後者を $`\mathscr R`$ と書く。商の切断 $`s`$、変更全体の始域関手 $`s`$、sort 添字 $`s`$ は定義域で区別する。
  - $`E`$ は第8章では評価対象、第9章では名前付き操作の集合である。第8章の $`J`$ は図式形、$`K_{\mathrm{fix}}`$ はその固定部分圏であり、第9章の $`K`$ は垂直変更群である。
  - 第9章の保存冪等射 $`N`$ と第7章の nerve $`N_n`$ は添字と型で区別する。第9章の $`r_j`$ は連結成分 $`j`$ の根、$`\omega_v`$ は頂点 $`v`$ の追加観測、中心化群 $`C_L(M)`$ の $`L,M`$ は群とその部分群を表す。
- **第10–13章（descent・アリアドネ・変形・大域化）**：
  - 第11章の $`p,q`$ は塔の関手、$`\pi_i,\pi_{\mathrm{ob}}`$ は線形商写像、$`B_i`$ は頂点補正空間、$`B_i^{\mathrm{par}}`$ はパラメータの係数行列である。同章で $`S\subseteq T`$ と書く $`T`$ は許可範囲、参照変更 $`h\mapsto h-a`$ の $`a`$ は基準の差を表す。
  - 第11章の $`P`$ は固定部分であり、第12章の $`P=k[x_1,\ldots,x_n]`$ は周囲多項式環である。第11章の $`A_v`$ は射影の核の可換群、第12章の $`A`$ はチャートの座標環である。
  - 第11章の $`S\subseteq\mathsf E`$ は許可範囲、第13章の $`S_i`$ は解集合である。第11章の $`R_i`$ は公開アフィン関係であり係数環 $`R`$ と区別する。第12章の $`R_{\mathrm{rep}}(U)`$ は修復語の関係群であり、第13章の $`D_n`$ は複体であって部分操作の定義域とは型で区別する。
- **第14–16章（輸送・正規化・診断）**：
  - 第15章の $`\Gamma,\Delta`$ は適合する変更の部分群であり、変数文脈や第16章の Laplacian $`\Delta_n`$ とは別である。
  - 第16章の $`S`$ は Source、$`L`$ は読み出しの有限添字集合、$`L_\bullet`$ は退化部分複体を表す。同章16.3節の $`G`$ はセル係数系、$`P`$ はそのコチェイン複体、$`\Gamma_e`$ は辺の持ち上げの関係グラフ、$`\mathscr R`$ はファイバー類の適合部分空間である。16.5節の $`G`$ は実際の被覆グラフ、$`P=L\times S`$ は実際の係数の原始生成元集合であり、各節で型を指定し直す。$`T`$ は16.1節では reading の値集合、16.3節では直接比較の $`H^1`$ 射である。
  - $`D_q`$ の添字 $`q`$ は reading である。定理16.25で局所的に使う $`q:Q_c\to Q_f`$ は交差余核の比較写像を表す。そこでの $`Z`$ は交差からの像であり、定理11.23・18.17の閉補正 $`Z=\ker d^1`$、次数付きコサイクル群 $`Z^n`$、根スキーム $`Z_{\sigma,\ell}`$ とは定義域と添字で区別する。
  - 付録Dでは、係数スキームの変更 $`B'\to B`$ による引き戻しと、同じ担体のフレーム変更を区別する。後者の共役は式(6.4)の右作用 $`A\mapsto g^{-1}Ag`$ に従う。
- **第17–19章・付録E（観測・修復方程式・再構成・費用）**：
  - 第18章の $`N=\ker L`$ と第19章の読み取り関手 $`N`$ は別の記号である。第19章の組み立て関手は $`\mathsf{Asm},\mathsf{Asm}_\sigma,\mathsf{Asm}_H`$ と書く。
  - 第18章の $`S`$ は候補辺の許可範囲、$`P_S`$ は補正空間であり、原始表示 $`\mathcal P`$ とは異なる。
  - 第19章の $`J`$ は Artin 試験では残差イデアル、図式補完では小圏を表す。
  - 第18章の階数計算や第19章のハンケル表で使うブロック行列の文字は、各設定・証明内で定義する。小行列式の開集合上で選ぶブロックや逆行列は局所的な計算用であり、実現の大域的な基底を指定するものではない。
  - 付録Eの $`c(\gamma),d(a,b)`$ は変更経路の費用とその下限であり、第11–18章のコチェイン微分 $`d^i`$ や固定図式 $`d`$ とは区別する。
