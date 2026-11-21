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
| $`\Gamma=(x_i:s_i)_{i=1}^n`$ | 有限の変数文脈 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`X_s(A)`$、$`X_\Gamma(A)`$ | 構造のsort担体と入力の積 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`D_p^A`$、$`G_p^A`$ | 部分操作の定義域とgraph | [1.2](part_1/chapter_1_atoms_laws_theories.md#12-型操作関係部分操作量の宣言) |
| $`\mathrm{Def}_t`$、$`E_t(\boldsymbol x,y)`$ | termの定義可能性と値を表す正の式 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\mathrm{ev}_A(t,\gamma)`$ | 入力 $`\gamma`$ でのtermの部分評価 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`I_\ell^A`$、$`\rho_\ell`$ | Lawの入力集合と、環値等式の場合の残差 | [1.3](part_1/chapter_1_atoms_laws_theories.md#13-lawの入力式評価充足) |
| $`\mathrm{Str}_\Sigma`$、$`\mathcal A_{\mathbb T}`$ | 構造の圏と必須Lawを満たす意味圏 | [2.1–2.2](part_1/chapter_2_models_and_morphisms.md#21-状態操作関係を持つ構造) |
| $`u:\mathbb T\to\mathbb T'`$、$`u^*`$ | 理論解釈と反対向きのモデル引戻し | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`\mathcal A_{\mathrm{tot}}`$ | 理論とモデルをともに動かす全体圏 | [2.3](part_1/chapter_2_models_and_morphisms.md#23-構造保存射と理論の解釈) |
| $`o_A:X_s(A)\to O`$ | 指定sortの状態の観測 | [2.2](part_1/chapter_2_models_and_morphisms.md#22-lawを満たすモデルと観測) |
| $`U`$、$`\mathcal A(U)`$、$`A\vert_U`$ | 宣言文脈、そのモデル圏、制限 | [3.1–3.2](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`\mathrm{Supp}(\ell)`$ | Lawの入力と結論を読むための宣言の支持 | [3.1](part_1/chapter_3_contexts_and_local_models.md#31-依存に閉じた文脈とlawの支持) |
| $`K_s`$、$`Q_s=R^{m_s}/K_s`$ | 生成元付き加群のkernelと商加群 | [3.3](part_1/chapter_3_contexts_and_local_models.md#生成元付き加群への適用) |

合成は $`(g\circ f)(x)=g(f(x))`$ の順で書く。
$`u:\mathbb T\to\mathbb T'`$ のモデル引戻しは
$`u^*:\mathcal A_{\mathbb T'}\to\mathcal A_{\mathbb T}`$ である。
宣言の包含 $`V\subseteq W`$ のモデル制限も $`\mathcal A(W)\to\mathcal A(V)`$ とする。
$`\Gamma`$ は変数文脈、$`U,V,W`$ は宣言文脈であり、両者を区別する。

後続で係数を指定する際には、基礎環を $`k`$、$`k`$ 代数を $`R`$、
係数的実現方式を $`\sigma`$、診断係数を $`\Lambda`$ と書く。
原始表示 $`\mathcal P`$、固定部分 $`K_{\mathrm{fix}}`$、評価対象 $`E`$ は別の記号とする。
一つのモデルの状態、モデルを動かすパラメータ、モデル間の変更は、それぞれの担体で扱う。
