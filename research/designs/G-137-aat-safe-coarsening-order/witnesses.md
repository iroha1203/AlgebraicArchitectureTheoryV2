# G-137：指定評価と回帰

W0–W3の原始データと評価項目は[GOAL E](../../goals/G-137-aat-safe-coarsening-order.md)の固定要求である。
W1・W2は未検証の候補であり、安全性・極大性・固定点の有無について期待値を入力しない。
全例に[同じ商規則](primitive-quotients.md#2-許す粗化と商の規則)を適用する。

## W0. 最大元を持つ正の基準例

S=T=Unit、q=id、V={0,1}、E={(0,1)}、両chart台はTとする。
Lawは一つの定数Lawを明示する。
全分割対の実比較を評価し、最大全関係が安全な最大元であり、
自己同型に固定されることを証明する。Bの成立側の出力をこの同じ入力で確認する。

## W1. 巡回向きを持つ四角形

S=T=Bool、q=id、V=ℤ/4ℤ、辺は $`i\to i+1`$ の四本、全chart台はT、面は空とする。
target分割Pは全二通りを候補集合に含める。
指定する四粗化 $`R_i=(\Delta_T,Q_i)`$ では、Q_iはiとi+1だけを併合する。
Q_i以外のchart分割も、全候補集合から除かない。

Law $`\ell(s)=s`$ はPが等号関係の段で用い、二つの発生ラベルを保持する。
Pが全関係の段では定数Lawを使う。全Law条件はAの一般定理で保証する。
fineのperiodは $`\operatorname{per}(z)=\sum_{i\in\mathbb Z/4\mathbb Z}z(i,i+1)`$ とし、
辺0→1で1、他辺で0のcochainを指定する。既存H¹での非零性を示す。

同じ原始表について、次を確定する。

1. 各R_i・各Aの実H¹写像とJ、各R_iの安全性・極大性の真偽。
2. 全分割対から得るMaxSafeと、最大元の有無。不存在と判定する場合は全共通上界の排除まで接続する。
3. 回転 $`i\mapsto i+1`$ とBoolの交換の作用、および全Aut(M)に対するFixMax。
4. Bの有限出力と、period・部分セル像からの評価の一致。

R10にある「四つの辺縮約が全極大元」「D₄の一軌道」という予想をここでは仮定しない。
この入力は有向閉路であり、反射が向きを保つ自己同型かどうかを無向図から推定できない。
原始有向辺を保つ置換を用いて作用を確定する。

## W2. 六角形の二つの併合

S=T=Bool、q=id、V={a,b,c,d,e,f}、辺は
$`a\to b\to c\to d\to e\to f\to a`$ の六本、全chart台はT、面は空とする。
Pが等号関係のときの非定数Lawと、全関係のときの定数LawはW1と同じものを使う。

R_acはchart a・cだけ、R_dfはd・fだけを併合し、ともにtarget分割は等号関係とする。
両者のjoin、さらにそれらの全共通上界もT0の全分割対の中で取る。
fineのperiodは六辺の値の和、指定cochainはa→bだけ1とする。

| 評価対象 | 必要な結果 |
| --- | --- |
| R_ac、R_df、そのjoin | 全Aの実H¹比較、rank、核・余核、Jと安全性の確定 |
| join閉性の候補 | 両者が安全でjoinが不安全なら、同じjoinの失敗領域と非零類を示す。それ以外なら、その確定した評価を記録する |
| 最大元不存在の候補 | 全共通上界を分類する。安全なものがあれば具体的に示し、なければ全排除を証明する |
| Lawとの接続 | 該当値blockと実Law比較、ラベルの重複度、指定periodの評価を同定する |

R10の数値案「個別は零欠損、同時併合はhidden=1」は未検証の予想として扱う。
この規則では逆向き辺を保持するため、向きを忘れて平行辺を一本にする規則の検算を転用しない。
候補の成立・不成立のいずれもEの評価結果として受け入れる。
Dの一様主張を決着する証拠には、実際に条件が揃ったものだけを使う。

## W3. G-136の台に依存するhiddenの再利用

G-136の [WidthInput.lean](../../lean/ResearchLean/AG/AtlasGluingWidth/WidthInput.lean) の
`Width.fineReading 2`、`Width.fine 2 false` と、辺a₀だけを除く `Width.fine 2 true` を使う。
S=T=(ℤ/2ℤ)×Bool、q=id、chartは $`v_i,w_i`$、台は

```math
S(v_i)=\{i\}\times\mathrm{Bool},\qquad
S(w_i)=\{i,i+1\}\times\mathrm{Bool}.
```

minusの辺は $`a_i:v_i\to w_i`$、$`b_i:w_i\to v_{i+1}`$。
plusはa₀だけを除き、他の入力を保つ。どちらもT0の有向単純nerveであることを示す。
粗化Rのtarget分割はfstの核、chart分割は全関係とする。
商targetをℤ/2ℤ、商chartをUnitへ同定すると、商台は全targetで辺は空となる。

新しく生成するm_R・u_R・T_Rを、G-136の
`Width.comparison 2 false/true` と `Width.actualMap` へ同定する。
その上で次の既存結果を再利用する。

- `Width.plus_defect`：plusの全AでJ=(0,0)。
- `Width.proper_defect`：minusの全真部分集合でJ=(0,0)。
- `Width.full_defect`：minusの全targetでJ=(0,1)。
- `Width.gluing_hidden_nonzero`、`Width.coefficient_hidden_same`：同じhidden類とG-135のfiber項への対応。

必要なのは、このRを全粗化の有限構成へ入力して同じ実比較・判定値が得られる接続である。
既存の全有限幅の分離定理や、局所J零の下で大域J零とq同型・Z零が同値になる定理を、
G-137の新規成果として数えない。
ここでの二領域の和と、W1・W2の二分割のjoinは異なる操作である。

## 回帰の焦点

| 誤った置換 | 検出する評価 |
| --- | --- |
| H¹次元の一致を同型とする | 同じ実比較のrank、核・余核代表を検査する |
| fine入力からの商写像を忘れ、同型な粗nerveを一つにする | W1の分割と自己同型による輸送を保持する |
| 一辺縮約だけを全極大元とする | W1で全分割対を比較する |
| 一つの不安全joinから最大元不存在を結論する | W2の全共通上界を調べる |
| 一つの非自明軌道から固定点不存在を結論する | W1で全MaxSafeを覆う |
| 非空Aは全て同じグラフだと仮定する | W3のproper/fullで異なる同じ実比較を再現する |

G-133の相殺例、G-134の混在面の例、G-135の非零transgressionの例は、
元の型と原始入力を保って再利用対応表で区別する。T0へ無理に変形して新しい指定例にはしない。
