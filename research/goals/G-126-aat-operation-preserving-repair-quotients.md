# G-126-aat-operation-preserving-repair-quotients — 操作と観測を保つ修復商の分類と有限構成

- `id`: `G-126-aat-operation-preserving-repair-quotients`
- `status`: `completed`
- `research mode`: `target-theorem`
- `tracking issue`: [#4945](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4945)
- `source note`: [n1016 §2.1・候補01](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [A–Eの実装設計](../designs/G-126-aat-operation-preserving-repair-quotients/README.md)

## 研究目的

状態の不一致を同一視して修復するとき、指定した操作と観測を保てる条件と、
可能な修復の全体を明らかにする。必要な同一視を生成する合同関係と、すべての
操作列の後も観測で区別できない合同関係を同じ順序で比較し、修復商の存在・分類・
要求の合成・有限構成を一つの定理から導く。

[G-103](G-103-aat-canonical-resolution.md)と
[Rising Sea 定理3.4](../../outreach/paper/rising-sea/ja/06-resolution-invariance.md)の
標準解像度は、現在のLaw評価を保つ最も粗いreadingを与える。ここでは名前付き操作と
同一視要求を加え、操作を降下できるreadingの全体を分類する。一般の同値関係の商と
束を用い、AAT側では同じsourceのLaw評価、操作経路の不一致、readingの因子化へ接続する。
G-124の局所再構成とは異なる、修復によって生成する商を研究対象とする。

## 固定target

A–Eを一つの分類・構成定理の構成部分とする。量化順は、任意の有限操作系と観測、
その系への任意の同一視要求、その修復商および構造保存写像とする。
有限集合には空集合も許す。

### A. 入力と二つの操作合同関係

有限集合 `S`、有限な操作名集合 `E`、全域写像族 `T_e:S→S`、集合 `O`、
観測 `o:S→O`、関係 `R⊆S×S` を入力とする。`S,E` は列挙と等号判定を持ち、
`T,o,R` は有限表で与え、`O` の等号を判定できるものとする。
`O` 自体の有限性や、各操作が現在の観測値を不変にすることは要求しない。
空語を含む有限語 `w∈E*` の作用は `T_ε=id`、`T_{we}=T_e∘T_w` とする。

操作合同関係は、`S` 上の同値関係 `θ` であって、任意の `e∈E` と `x,y∈S` に対し
`x θ y ⇒ T_e(x) θ T_e(y)` を満たすものとする。その全体 `Con_T(S)` を包含で順序づけ、
完全束を構成する。次の二つを元の入力から構成する。

```math
\theta_R=\bigcap\{\theta\in\mathrm{Con}_T(S)\mid R\subseteq\theta\},
\qquad
x\,\beta_o\,y\quad\Longleftrightarrow\quad
\forall w\in E^*,\quad o(T_w(x))=o(T_w(y)).
```

`θ_R` は `R` を含む最小の操作合同関係、`β_o` は `ker o` に含まれる最大の
操作合同関係であることを証明する。`ker o` は現在の観測値の一致を表す。

### B. 修復商の分類と普遍性

修復商は、全射 `q:S→Q` と、操作 `T̄_e:Q→Q`、観測 `ō:Q→O` であって

```math
qT_e=\bar T_e q,\qquad \bar o q=o,\qquad
\forall(x,y)\in R,\quad q(x)=q(y)
```

を満たすものとする。全射性から `Q` の有限性と、降下する操作・観測の一意性を導く。
修復商 `q,q'` の間の射は、操作・観測を保ち `f q=q'` を満たす写像 `f:Q→Q'`
すべてとする。各射の一意性と全射性も証明する。

`q↦ker q` と `θ↦(S→S/θ)` によって、`S` からの商写像と可換な同型までの修復商と

```math
\{\theta\in\mathrm{Con}_T(S)\mid\theta_R\subseteq\theta\subseteq\beta_o\}
```

の順序同型を構成する。順序の向きは、`q→q'` が存在することと
`ker q⊆ker q'` の同値で固定する。対応する射の恒等・合成も保持する。
この分類から次を導く。

1. 修復商の存在、`θ_R⊆β_o`、`θ_R⊆ker o`、`R⊆β_o` は同値である。
2. 存在する場合、`S/θ_R` は最も細かい修復商、`S/β_o` は最も粗い修復商であり、
   すべての修復商への前者からの射と、後者への射は一意である。
3. 存在する場合、任意の操作・観測付き集合 `X` と、操作・観測を保ち `R` を
   同一視する写像 `h:S→X` は、`S/θ_R` を通じて一意に因子化する。
   `X` の有限性と `h` の全射性は要求しない。

### C. 修復要求の合成と入力間の対応

同じ `S,T,o` 上の任意の有限族 `(R_i)_{i∈I}` に対し、

```math
\theta_{\bigcup_{i\in I}R_i}=\bigvee_{i\in I}\theta_{R_i},
\qquad
\text{各 }R_i\text{ が修復可能}
\ \Longleftrightarrow\ \bigcup_{i\in I}R_i\text{ が修復可能}
```

を証明する。空族のjoinは等号関係とする。
修復可能な `R_1,R_2` について、`R̄_2` を `S/θ_{R_1}` における `R_2` の像とする。
第一の商から降下した操作・観測に対し第二の生成合同関係を構成し、

```math
(S/\theta_{R_1})/\theta_{\bar R_2}
\ \cong\ S/(\theta_{R_1}\vee\theta_{R_2})
```

を、元の `S` からの商写像と可換な一意の操作・観測保存同型として構成する。
有限族のすべての順序と括弧づけに一般化し、二つの逐次商を結ぶ同型の合成が
直接の同型に一致することを証明する。

さらに、同じ `E,O` を持つ二入力 `(S,T,o,R)`、`(S',T',o',R')` の間の任意の写像
`h:S→S'` が `hT_e=T'_eh`、`o'h=o`、`(h×h)(R)⊆R'` を満たすとする。
`h` は `θ_R` を `θ_{R'}` へ、`β_o` を `β_{o'}` へ送り、両端の商写像を誘導することを
示す。両入力が修復可能な場合には、両端を結ぶ `S/θ_R→S/β_o` との平方も可換にする。
これらの対応は恒等と合成に整合し、入力の同型に対して商の同型を与える。

### D. 有限表からの判定・構成と不可能性の証拠

Aの表から両端 `θ_R,β_o` の分割を計算し、Bの存在条件を決定する停止する手続きを
構成する。成功時には両端の商の有限表、元の `S` からの商写像、降下した操作と観測、
両端間の因子化を返す。失敗時には

```math
(x,y)\in R,\qquad w\in E^*,\qquad
o(T_w(x))\ne o(T_w(y))
```

を満たす具体的な状態対と操作語を返す。この出力が修復商の不存在を証明することと、
不存在なら必ずこの出力が得られることを示す。`n=|S|` とすると、失敗時の語は
`|w|<n²` を満たすものを構成する。現在の観測だけで異なる場合は空語を許す。

入力は、番号づけた `n` 状態・`m=|E|` 操作、`m×n` 個の遷移先、`n` 個の観測値、
`n×n` の要求の真偽表とする。表参照、番号・真偽値の基本演算、観測値の等号判定を
それぞれ単位費用とする。このモデルで、両端の構成・存在判定・成功または失敗の出力を
合わせた最悪時の費用に `O((m+1)(n+1)^5)` の上界を証明する。
停止・正確性・費用は同じ手続きについて証明し、Bの分類へ接続する。

### E. Lawの標準解像度と操作経路の修復への接続

任意の有限Law族 `L` と評価 `v_ℓ:S→Val_ℓ` に対し、
`O=∏_{ℓ∈L}Val_ℓ`、`o(x)=(v_ℓ(x))_ℓ` とする。
`L` の列挙と各 `Val_ℓ` の等号判定を入力に含める。
既存の `FiniteLawFamily` と同じ評価から `jointKernelReading` を作り、これを `q_L` と書く。

Bの修復商を、既存の `Reading S` のうち、各操作を降下でき、`L`-adequateであり、
`R` を同一視するものすべてと対応させる。因子化の写像を既存の `Reading.FactorsThrough`、
`Reading.CoarserThan` と照合する。Aから構成する `q_β:S→S/β_o` はこのLaw族にadequateであり、
`q_L.CoarserThan q_β` を満たすこと、さらに

```math
\ker q_L=\beta_o
\quad\Longleftrightarrow\quad
\ker q_L\text{ がすべての }T_e\text{ に安定}
\quad\Longleftrightarrow\quad
\text{すべての }T_e\text{ が }q_L\text{ に沿って降下する}
```

を証明する。操作名集合が空の場合には `β_o=ker q_L` となり、`q_β` とG-103の
標準解像度は、元の `S` からの写像と可換な一意の同型で対応する。任意の修復可能な
`R` について、Dの返す最も粗い修復商も同じ核を持ち、この一意の同型で対応する。

有限な操作経路対の族 `P⊆E*×E*` から要求を

```math
R_P=\{(T_p(x),T_q(x))\mid(p,q)\in P,\ x\in S\}
```

として生成する。この要求にB–Dを適用して修復可能性を判定し、修復可能な場合には
商での各経路の等式 `T̄_p=T̄_q` と全Law評価の降下を導く。修復商の全体は、
この経路等式と操作・Law評価の保存を満たす
すべての全射と一致することを示す。Cの写像はLaw評価と経路作用を保つ写像として対応させる。
ここで構成する射はsource上の状態商とreadingの因子化であり、非単射の商写像も含む。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 有限操作系、観測、要求と有限表：A | 入力として保持 | Aの全域操作・列挙・等号判定 | 両端の構成からDの計算まで |
| 操作合同関係の束、`θ_R,β_o`：A | 構成・証明義務 | Aの最小性・最大性 | Bの分類、Cのjoin、Dの正確性 |
| 修復商と構造保存写像の条件：B | 分類対象の定義 | Bの式と全射性。両端の具体的構成ではこれらを証明 | 原始入力から商を作り、Bの全分類へ |
| 修復可能性：B・C | 両端の普遍性・逐次修復の一般定理の仮定 | Bの存在条件で特徴づけ、Dで決定、指定例で証明 | 観測の降下と逐次商の構成へ |
| 有限族・入力間の写像：C | 有限族と写像の保存式を入力として保持 | Cの合同関係・商・同型の誘導は構成義務 | 要求の合成と入力変更への整合 |
| 有限手続き・失敗の語・費用：D | 構成・証明義務 | Dの停止・正確性・上界 | Aの原始表からBの存在・不存在へ |
| Law族と経路対：E | 評価・経路対を入力として保持 | `R_P`、Lawの降下、readingの対応は構成・証明義務 | 既存の標準解像度とA–Dの接続へ |

## 既存構成の参照

- [Reading.lean](../lean/ResearchLean/AG/CanonicalResolution/Reading.lean)：
  `Reading`、`Reading.factorsThrough_iff_coarserThan`、`FiniteLawFamily.adequate_iff_kernel`。
- [JointKernel.lean](../lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean)：
  `FiniteLawFamily.jointKernelReading`、`jointKernel_kernel_iff`、`jointKernel_universal`。
- [Effective.lean](../lean/ResearchLean/AG/CanonicalResolution/Effective.lean)：
  `FiniteLawFamily.computedReading`、`computed_kernelEquivalent_jointKernel`。
- [mathlibの同値関係と商](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Setoid/Basic.html)：
  `Setoid` の完全束と商の同型定理を再利用し、名前付き単項操作族への安定性を接続する。

## 完了条件

1. A–Eの一般定理、構成、計算の性質をLeanで証明し、次の固定例を同じ一般定理と
   Dの手続きへ接続する。達成として認める結果は `target-theorem-proved` とする。
2. **分類と合成の例**：`S={0,1,2,3}`、一操作 `T=(01)(23)`、
   `o(0)=o(1)=0`、`o(2)=o(3)=1`、`R_1={(0,1)}`、`R_2={(2,3)}` とする。
   `θ_{R_1}` の分割が `{0,1}|{2}|{3}`、`β_o` が `{0,1}|{2,3}` であることを計算し、
   `R_1` の修復商がBの同型までちょうど二つあることを示す。
   `θ_{R_1}∨θ_{R_2}=β_o` と、両順序の逐次修復・一括修復の商写像を計算する。
   同じ観測を一つのLaw評価に取り、Eのadequacyとreadingの因子化にも接続する。
3. **将来の観測による不可能性の例**：`S={a,b,c}`、
   `o(a)=o(b)=0`、`o(c)=1`、`T(a)=a`、`T(b)=T(c)=c`、`R={(a,b)}` とする。
   `β_o` は等号関係、`θ_R` は全関係であることを示す。Dが返す証拠に加え、
   空語では分離できず一文字の語 `T` で分離できることを証明する。
   観測を一つのLaw評価に取り、`q_L` には操作が降下しないことをEへ接続する。
4. **経路要求からの生成**：条件2の `S,T,o` と `P={(ε,T)}` を使う。
   Eから生成した `R_P` の合同関係が `β_o` に一致し、修復商で `T̄=id`、
   商の状態数は2、Law評価は非定値であることを証明する。
5. Lean成果を `research/lean/ResearchLean/AG/` に置き、
   `research/reports/G-126-aat-operation-preserving-repair-quotients.md` にA–Eと宣言、
   前提の出所・使用先、有限例、計算費用の証拠を対応させる。
6. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
