# G-132-aat-visible-cycle-reflection — 可視閉路による修復障害の零性反映

- `id`: `G-132-aat-visible-cycle-reflection`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5250](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5250)
- `source note`: [n1016 §5.3・候補06](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [構成・証明方針](../designs/G-132-aat-visible-cycle-reflection/README.md)、[再利用対応表](../designs/G-132-aat-visible-cycle-reflection/reuse-map.md)、[実被覆と指定例](../designs/G-132-aat-visible-cycle-reflection/witnesses.md)

## 研究目的

Law値の診断が整数係数の修復障害の零性を反映するために、被覆のどの閉路を各ラベルで
読めばよいかを必要十分条件で定める。同じ原始入力から作った既存障害類と診断類について、
整数補正・実際の貼り合わせ、反映が失敗する実入力、有限判定を得る。

[G-125](G-125-aat-obstruction-diagnostic-bridge.md)は、関係成分を識別する条件と
全chartに共通するラベル代表から零性反映を証明した。今回は関係成分の識別を保ち、
共通代表の条件をラベルごとの閉路可視性へ置き換える。
既存のlaw-generated診断と実Čech比較を使い、その比較が情報を失わない条件を求める。

## 固定target

T0の構造を任意に固定し、その構造の下で全局所データを量化する。A–CとW1–W3を
一つの定理・構成群として証明する。A–Cの主張は研究targetであり、既証明の表示ではない。

### T0. 原始入力、実被覆、量化範囲

有限集合 `Source`、有限Law族 `laws`、全射reading $`q:S\to Q`$ とそのadequacy、
生成子 $`G=\mathrm{Law}\times S`$ のラベルを保つ原始関係 $`R`$ を固定する。
$`\Lambda`$ はSourceで実際に現れるLaw・値の組とする。同ラベルの任意の二生成子が
$`R`$ の対称・反射・推移閉包で結ばれる条件 $`R_q`$ を入力条件とし、
$`M_R=\mathbb Z^{(G)}/\langle e_g-e_h:gRh\rangle`$ を原始関係から構成する。

位相空間 $`X`$ の開集合からなる有限非空な順序付きchart族 $`(U_i)_{i\in I}`$ を取る。
各chartは非空連結、$`\bigcup_iU_i=X`$、非空二重交差は連結、相異なる三chartの
交差は空とする。nerve $`N`$ の頂点は全chart、辺は **すべての**
$`i<j`$ で $`U_i\cap U_j\ne\varnothing`$ となる組であり、向きを $`i\to j`$ とする。
交差点の選択は辺の重複を作らない。$`N`$ は単純グラフで、複数の連結成分を許す。

各chartに非空の原始target台 $`T_i\subseteq Q`$ を指定し、実在する辺 $`e=(i,j)`$ の
診断台を $`T_e=T_i\cap T_j`$ とする。幾何台 $`U_i\subseteq X`$ とtarget台
$`T_i\subseteq Q`$ は異なる入力である。辺の有無は実交差で決まり、target台の交差だけ
では辺を作らない。この同じセルと台から `TargetSupportedNerve` を構成する。
各 $`\lambda=(\ell,v)\in\Lambda`$ について

```math
\begin{aligned}
V_\lambda&=\{i:\exists t\in T_i,\ \bar v_\ell(t)=v\},\\
E_\lambda&=\{e:\exists t\in T_e,\ \bar v_\ell(t)=v\}
\end{aligned}
```

から部分グラフ $`N_\lambda`$ を生成する。同じtargetが交差台に属することを要求し、
両端で別々のtargetが同ラベルを持つだけでは可視辺にしない。孤立可視頂点・空の可視部分も扱う。

point Atomと生成子Atom、原始関係、開集合への台とrestrictionからAATの実被覆・
局所定数 $`M_R`$ 値の係数層 $`F_R`$ を構成する経路をAに含める。
局所データ $`x=(\xi,p)`$ は、実重なり上の $`F_R`$ の全整数アフィン遷移切断
$`\xi`$ と、各chart上の $`F_R`$ の全切断 $`p`$ である。
ここで「実」は実在する層・切断を指し、係数は $`\mathbb R`$ ではなく $`M_R`$ である。
相異なる三重交差がないため、任意の辺遷移を許し、逆向きは符号反転、自己遷移は零とする。
$`q,R,U_i,T_i`$ を固定したまま **$`\xi,p`$ の双方を量化する**。

### A. 既存障害・独立に生成した診断・可視部分の比較

同じ原始入力から、実restrictionを持つ `FaceEmptyAATCechCover`、
`faceEmptyCechComplex`、既存 `GluingMismatchData` と
`existingDescentObstructionClass` を構成する。実被覆のadmissibility、台の連続性、
全非空交差の収載、幾何的三重交差の空性を証明してこの経路へ渡す。
供給されたface型の空性だけでこれらの義務を代替しない。

既存障害類を加法的H¹へ移した類を $`o(x)`$ と書く。その代表は
$`z(x)=\xi+d^0_{\mathrm{ob}}p`$ である。診断は既存の
`TargetSupportedNerve.lawGeneratedComplex` を使い、同じ遷移と状態のLaw評価から
$`\phi^1\xi+d^0_{\mathrm{diag}}\phi^0p`$ を生成し、その類を $`a(x)`$ とする。
生成子・関係と実restrictionから次数0–2の比較 $`\phi`$、誘導加法準同型 $`\Phi`$ を作り、
$`\Phi(o(x))=a(x)`$ を証明する。診断をこの等式の右辺となるように再定義しない。

$`R_q`$ から $`M_R\cong\mathbb Z^\Lambda`$ を導き、実Čech複体を
$`C^\bullet(N;\mathbb Z^\Lambda)`$、診断複体を
$`\bigoplus_{\lambda\in\Lambda}C^\bullet(N_\lambda;\mathbb Q)`$ に同定する。
両同定はcochain、微分、商の代表元で対応させる。特に比較の各成分が

```math
H^1(N;\mathbb Z^\Lambda)
 \longrightarrow H^1(N;\mathbb Q^\Lambda)
 \xrightarrow{(\operatorname{res}_\lambda)_\lambda}
 \bigoplus_{\lambda\in\Lambda}H^1(N_\lambda;\mathbb Q)
```

であることを、既存の `actualCechDiagnosticH1Map` について証明する。
最初の写像は整数から有理数への係数変更であり、元の比較は加法準同型として扱う。

### B. 零性反映の必要十分条件と実修復

T0の各固定構造について、次の三条件を同値にする。

```math
\begin{aligned}
\mathrm{(B1)}\quad&\forall x=(\xi,p),\quad a(x)=0\ \Longleftrightarrow\ o(x)=0,\\
\mathrm{(B2)}\quad&\forall\lambda,\quad
 H_1(N_\lambda;\mathbb Q)\longrightarrow H_1(N;\mathbb Q)
 \text{ は全射},\\
\mathrm{(B3)}\quad&\forall\lambda\ \forall e\in E(N),\quad
 e\text{ が橋でない}\ \Longrightarrow\ e\in E_\lambda.
\end{aligned}
```

橋は無向グラフからその辺を除いたときに連結成分数が増える辺とする。
写像(B2)は部分グラフ包含のchain写像から作る。

これらの条件と $`a(x)=0`$ の下で、実chart切断の整数補正 $`n`$ を構成し、
$`d^0_{\mathrm{ob}}n=z(x)`$ を証明する。アフィン遷移 $`\xi`$ から状態の層
$`\mathcal T_\xi`$ と局所自明化を構成し、補正後の $`p-n`$ がその局所表示で
一致すること、大域切断へ一意に貼り合うことを示す。零障害・整数補正の存在・
$`\mathcal T_\xi(X)`$ の非空性を同値にする。

必要性は、任意の不可視非橋辺 $`e`$ とラベル $`\lambda`$ から、その辺上だけ
$`\xi_e=u_\lambda`$（$`\mathbb Z^\Lambda`$ の基底の逆像）、他辺と $`p`$ は零という
**実切断の局所データ**を構成して示す。診断cochainが零である一方、$`e`$ を一度通る
閉路のperiodが $`\pm u_\lambda\ne0`$ となり、既存障害類が非零であることを証明する。
全H¹類の実現可能性を入力仮定にせず、この構成を証明義務とする。
固定 $`\xi`$ で $`p`$ だけを変更しても類が変わらないことも対応させる。

### C. 有限表からの判定と失敗証拠

有限Source・Law評価・reading・原始関係・target台と、実被覆の点・開集合・交差を
表す有限表を入力とする。T0を満たす表について、$`N,N_\lambda`$ を生成し、
橋の判定と全ラベルでの包含検査から(B1)の真偽を返す停止手続きを構成する。
幾何台とtarget台の表を区別し、交差・台・関係・ラベルの等号を有限に検査できる表示を使う。

成功を返すことと(B1)–(B3)の成立を同値にする。失敗時には
$`(\lambda,e,\gamma,x)`$ を返し、$`e`$ の不可視性・非橋性、$`\gamma`$ がその辺を一度通る
閉路であること、およびBの零診断・非零既存障害を、同じ表から生成した実入力で証明する。
抽象的な有限性や場合分けだけでなく、表の列挙・探索から出力する手続きとその正確性を示す。
計算量の最適化は要求しない。

### W. 同じA–Cへ接続する指定例

全例で有限Alexandrov空間の頂点 $`\le`$ 接続辺点を用い、実被覆・Atom・Law・
関係・台・restriction・係数層・既存障害類まで構成する。有限表とA–Cへの適用を揃える。
以下のグラフ・ラベル可視性・局所データを固定し、具体的な台の表示は[指定例](../designs/G-132-aat-visible-cycle-reflection/witnesses.md)で与える。

- **W1**：頂点 $`0,1,2,3`$、辺 $`01,02,12,23`$。ラベル0は全頂点・全辺、
  ラベル1は三角形 $`012`$ だけで可視とする。共通代表条件が偽で(B1)–(B3)は真、
  $`H_1(N;\mathbb Q)\ne0`$ を同時に示す。$`p=0`$、
  $`h=(0,u_1,0,u_1)`$、$`\xi=d^0h=(u_1,0,-u_1,u_1)`$ に対し、
  非零mismatchの整数補正と実際の貼り合わせを示す。
- **W2**：頂点 $`0,1,2,3,4`$、辺 $`01,02,12,03,04,34`$ の二三角形を
  頂点0で接続する。ラベル0は全体、ラベル1は三角形 $`012`$ だけで可視とする。
  $`\xi_{34}=u_1`$、他辺と $`p`$ は零とし、診断cochain零、閉路 $`0,3,4,0`$ の
  period $`u_1\ne0`$、既存障害類非零、Cの失敗出力を同じ入力で示す。
- **W3**：道 $`0-1-2`$、ラベル0は全体、ラベル1は頂点0だけで可視とする。
  ラベル1に可視辺がなくても(B1)–(B3)が成立することと、辺 $`12`$ の非零遷移の
  整数補正・貼り合わせを示す。森のこの例は、閉路を持つW1・W2と併せて要求する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 有限Source・Law、adequate reading、原始関係、$`R_q`$ (T0) | 原始入力として保持。Wでは証明義務 | 同ラベル生成子の関係経路 | 係数座標、基底の非零性、A・B |
| 実有限被覆の連結性・交差条件、固定target台 (T0) | 入力幾何として保持。W・Cの表では構成・検査義務 | 実交差と完全なnerve、K1の台 | Aの正規化と可視部分 |
| AAT site・係数層・被覆・連続性・既存類 (A) | 原始入力からの構成・証明義務 | Aの実restrictionと既存障害の対応 | Bの実入力・整数補正・貼り合わせ |
| ラベル分解・可視グラフ同定・実比較 (A) | 既存分解を再利用し接続を証明 | cochain・微分・商の同定 | (B2)と診断の零性 |
| (B2)・(B3) | 十分性の方向仮定。必要性・Cでは結論／判定対象 | Bの三条件同値 | 全局所データでの(B1) |
| 有理大域potential・整数補正・状態層 (B) | 構成・証明義務 | 可視閉路から全閉路、実切断への復元 | 既存障害の零性と大域状態 |
| 不可視非橋辺からの実局所入力 (B) | 構成・証明義務 | 単一辺の基底遷移と非零period | (B1)から(B3)、Cの失敗証拠 |
| 有限表・探索・出力の意味 (C) | 表は入力、停止・正確性・実入力復元は証明義務 | Cの成功同値と失敗出力 | Wと一般定理の計算可能性 |
| W1–W3 | 全前提と指定結論の構成・証明義務 | 同じ実被覆・Law・台・遷移 | A–Cの非空虚な適用 |

結論との循環の確認対象は、Aの比較・台・被覆の選択、Bのpotentialと実入力の生成である。
共通代表、比較の単射性、全H¹類の実現可能性を入力recordへ追加してこれらを放電したことに
しない。固有の生成経路はA・Bに定め、共通の弱化検査は下記基準を参照する。

## 完了条件と停止条件

1. A–Cの全構成、Bの三条件の全方向、整数補正と実貼り合わせ、W1–W3をLeanで証明する。
   達成として認める結果は `target-theorem-proved` とする。
2. Lean成果を `research/lean/ResearchLean/AG/VisibleCycleReflection/` に置く。
   `research/reports/G-132-aat-visible-cycle-reflection.md` に条項と宣言、入力からの生成、
   前提の出所・使用先、既存APIとの対応、有限表と実行結果を対応させる。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportで管理する。
4. 固定主張への反例は `target-refuted`、必要な構成が未接続なら未完了として記録する。
   targetの仮定追加・量化縮小・必須例の差し替えが必要なら `goal defect` で停止し、
   人間へ理由と改訂案を報告する。その他の停止処理は共通基準に従う。

非目標は、非定数局所係数、torsion、2-cell、$`R_q`$ を欠く係数衝突、最小観測費用、
reading変更に関する新しい自然性である。対象はT0のAAT実被覆とその診断であり、
任意のコード依存グラフへの適用やソース抽出完全性へ量化を広げない。
