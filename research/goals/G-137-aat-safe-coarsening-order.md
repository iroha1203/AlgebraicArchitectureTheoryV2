# G-137-aat-safe-coarsening-order — 安全粗視化の順序と自然選択の存在判定

- `id`: `G-137-aat-safe-coarsening-order`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5358](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5358)
- `source note`: [n1016 §4.3・候補12](../../docs/note/n1016_rising_sea_v2_paper_plan.md)、[n1006 R10](../../docs/note/n1006_aat_atlas_reinforcement_plan.md)
- `design`: [構成と証明方針](../designs/G-137-aat-safe-coarsening-order/README.md)、[原始入力と商](../designs/G-137-aat-safe-coarsening-order/primitive-quotients.md)、[判定と対称性](../designs/G-137-aat-safe-coarsening-order/selection-theorem.md)、[指定評価と回帰](../designs/G-137-aat-safe-coarsening-order/witnesses.md)、[再利用対応](../designs/G-137-aat-safe-coarsening-order/reuse-map.md)

## 研究目的

一つの細読みから得られる粗化のうち、すべての対象Law族の一次診断を保つものを
有限半順序として構成する。その全極大元を求め、最粗元の存在、最小共通粗化についての
閉性、同型に自然な極大元の選択が、それぞれ成り立つかを決着させる。

対象は、原ノートの環状例を含む、面を持たない有限有向nerveと支持台である。
粗化規則を先に固定し、結論の成立・不成立は研究の出力にする。
[G-133](G-133-aat-atlas-defect-composition.md)の比較合成、
[G-134](G-134-aat-face-relation-subdivision.md)の実比較生成、
[G-135](G-135-aat-atlas-coefficient-fiber.md)の保存判定を使い、
**同じfine入力から出る全粗化の順序と、その上の自己同型作用**を新たに扱う。
[G-136](G-136-aat-atlas-gluing-width.md)の領域貼り合わせとその具体例は回帰に使う。

## 固定target

T0・A–Eを一つの構成・判定定理群とする。
原始入力と商の定義は[設計の§1–4](../designs/G-137-aat-safe-coarsening-order/primitive-quotients.md)、
指定例のデータと評価項目は[指定評価のW0–W3](../designs/G-137-aat-safe-coarsening-order/witnesses.md)も固定要求に含める。

### T0. 入力クラスと安全性

入力 $`M=(S,T,q,V,E,(S_v)_{v\in V})`$ は、非空有限集合S・T・V、
全射reading $`q:S\twoheadrightarrow T`$、対角を含まない有向辺集合
$`E\subseteq V\times V`$、非空支持台 $`S_v\subseteq T`$ とする。
同じ向き・同じ両端点の辺は一つ、逆向きの辺は別セルである。
面型は空、辺台はK1の両端台の交差、係数はℚに固定する。
これらから既存の `TargetSupportedNerve` $`N_M`$ を構成する。

全粗化は、TとV上の**任意の**同値関係の対
$`R=(P_R,Q_R)\in\operatorname{Eq}(T)\times\operatorname{Eq}(V)=\mathcal R(M)`$ とする。
readingの商とchartの商は独立に選ぶ。
商台はchart fiber内の台の合併の像、商辺は異なる商chart間に残る有向辺、面は空とする。
内部辺をすべて縮約し、同じ向きの平行辺を一つにする規則を全Rで用いる。

$`R\le R'`$ は両関係の包含と定める。右ほど粗く、最粗元は最大元である。
商の名前の違いだけを、固定したMからの二つの商写像と可換な同型で同一視する。
Mの自己同型で交換される別の分割は、別の元として保持する。

各Rの商readingを $`q_R`$、商nerveを $`N_R`$、target商写像を $`\pi_R:T\to T/P_R`$ とする。
商セルから原始比較 $`m_R:N_M\to N_R`$ を生成し、すべての
$`A\subseteq T/P_R`$ で、既存の比較を用いて

```math
u_{R,A}:C^\bullet(N_R,A)\longrightarrow C^\bullet(N_M,\pi_R^{-1}A),
\quad T_{R,A}=H^1(u_{R,A}),\quad
J_{R,A}=(\dim\ker T_{R,A},\dim\operatorname{coker}T_{R,A})
```

を構成する。$`\mathrm{Safe}_M(R)\iff\forall A,\ T_{R,A}\text{ が全単射}`$、
$`\mathcal U(M)=\{R\mid\mathrm{Safe}_M(R)\}`$ とする。空Aを含める。
全単射性はこの実比較について判定する。

### A. 商の因子化、実比較、全Lawとの同値

全Rと全 $`R\le R'`$ について、商reading・K1台・部分セル像から既存の
`TargetSupportedNerveMorphism` とその `IncidenceSupportedComparison` への埋め込みを生成する。
商写像の因子化と関係包含の同値、二段の商と直接の商の同型、恒等・合成を証明する。
支持複体と実H¹比較の可換性では、R′の部分集合AをRへ引き戻す。

同じ比較について、T0の安全性を次の全Law条件と同値にする。
任意の `FiniteLawFamily S` とその $`q_R`$ へのadequacyに対して、
既存 `generatedComparisonH1Map` が全単射である。
細readingへのadequacyは導出する。Law族は商幾何の後に量化し、値型全体の有限性は仮定しない。
同じ台を持つ異なる発生ラベルも保持する。

さらに $`J_{R,A}=0`$、G-135の同じ比較の係数・fiber保存条件と同値にする。
この接続によって、以後の安全性判定を既存の実核・余核へ戻す。

### B. 全安全元と最粗元の有限分類

原始有限表から $`\mathcal R(M)`$、$`\mathcal U(M)`$、その極大元集合
$`\operatorname{MaxSafe}(M)`$ を尽くす有限構成を与え、正しさと完全性を証明する。
恒等粗化の安全性と、各安全元の上に極大安全元が存在することを示す。
任意に選んだ一つの極大元と、すべての安全元の上にある最大元を区別する。

各Mで、次の三判定を原始表から行い、結果に応じて右欄の証拠を構成する。

| 判定 | 成り立つ場合 | 成り立たない場合 |
| --- | --- | --- |
| 最大安全元が存在する | 具体的な $`R_*\in\mathcal U(M)`$ と全安全Rに対する $`R\le R_*`$ | 二つの安全元R・Sと、全 $`W\ge R,S`$ が安全でない証明 |
| $`\mathcal U(M)`$ は $`\mathcal R(M)`$ の二項joinで閉じる | 全安全R・Sについて $`R\vee S`$ の安全性 | 安全R・S、$`R\vee S`$ の部分集合Aと実比較の非零核または非零余核類 |
| 自己同型が固定する極大安全元が存在する | Cの $`\operatorname{FixMax}(M)`$ の具体的な元 | 全極大安全元Rについて、それを動かす具体的な自己同型 |

最大元存在は、有限性を用いて「極大元が一つ」および
「任意の二安全元が安全な共通上界を持つ」と同値にする。
join不安全だけから最大元不存在を推論せず、第一行の不成立では全共通上界を排除する。
有限構成には、各不安全Wの部分集合と実核・余核による失敗証拠も含める。

### C. 同型輸送と自然な選択

T0の入力間の同型 $`\alpha:M\cong M'`$ は、S・T・Vの全単射で、q、
有向辺関係、支持台を保つものとする。全同型を射とするgroupoidで量化する。
同値関係の輸送 $`\alpha_*`$ が順序、実比較、安全性、全極大元を保つことを証明する。
比較の共役図式は元のcochainとH¹写像で示す。

```math
\operatorname{FixMax}(M)=
\{R\in\operatorname{MaxSafe}(M)\mid
       \forall g\in\operatorname{Aut}(M),\ g_*R=R\}.
```

Mと同型な入力すべてに対する、全同型に整合する極大安全元の選択が存在することと、
$`\operatorname{FixMax}(M)\ne\varnothing`$ を同値にする。
固定元からの輸送が同型の選び方に依存しないことまで証明する。
自然な選択の出力はRそのものであり、自己同型軌道の選択ではない。

### D. 三つの一様主張の成立可否を決着する

量化域はT0の**全有限入力**で固定し、次の真偽をそれぞれ決める。
有限符号化として各集合を `Fin n` で表してよく、Cの全同型を維持する。

| 名前 | 決着すべき主張 |
| --- | --- |
| $`P_G`$ | すべてのMで $`\mathcal U(M)`$ に最大元が存在する |
| $`P_J`$ | すべてのMで $`\mathcal U(M)`$ がT0のjoinについて閉じる |
| $`P_N`$ | 全Mに極大安全元 $`s(M)`$ を割り当て、全同型で $`s(M')=\alpha_*s(M)`$ となる選択が存在する |

成立の場合は、$`P_G`$ では全Mに対する最大元の構成、$`P_J`$ では全M・全安全対の保存証明、
$`P_N`$ では全Mに対する選択とその自然性の証明を要求する。
不成立の場合は、原始有限表から作った具体的Mについて、Bの対応する不成立証拠を要求する。
$`P_N`$ の反証ではCから全groupoid上の選択不存在を導く。
反例入力はT0内で選べるが、粗化規則・安全性・許容同型の変更はできない。

結果は各主張について成立または不成立のどちらか一方を明記し、その側の証拠へ接続する。
一般入力の有限判定だけ、未評価の $`P\lor\neg P`$、答えを保持する入力certificateでは
この条項を満たさない。$`P_J\Rightarrow P_G\Rightarrow P_N`$ の接続も証明する。

### E. 指定評価と既存例への接続

[W0–W3](../designs/G-137-aat-safe-coarsening-order/witnesses.md)を同じA–Cの経路へ通す。
W0は正の基準例、W1・W2は四角形・六角形の候補の**成立判定**、
W3はG-136の台に依存する比較を新しい粗化入力へ同定する回帰である。
W1・W2の安全性・極大性・固定点について、指定の真偽を先に仮定しない。
各候補の評価が原ノートの予想と異なる場合も、同じデータの確定結果を成果に含める。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| T0の有限S/T/V・全射q・有向E・非空台・空面・ℚ | 入力として保持。Eでは構成義務 | 原始表、K1 | 商nerveと実微分 |
| T0の全同値関係対と商規則 | 固定する数学的対象 | 原始入力から全商を生成 | Aの因子化、Bの全候補 |
| 比較・合成・Law同値・係数分解への接続 (A) | 構成・証明義務 | 同じ原始部分セル像と既存宣言 | 安全性と失敗証拠 |
| 全列挙・最大性・全共通上界排除 (B) | 構成・証明義務 | 関係包含と実有理行列 | 各Mの判定、Dの反証 |
| 同型の全単射・q/E/台保存 (C) | 一般同型の入力条件。具体例では放電 | 元セルと支持点の輸送 | 安全posetへの作用 |
| 固定極大元 (C) | 存在方向の仮定。B・Dの適用では構成または全排除 | 全自己同型の作用 | 同型類上の選択 |
| Dの成立・不成立の確定 | 証明・反証義務 | 一様構成またはT0内の具体的反例 | 三つの主張の決着 |
| W0–W3の原始表・類・軌道 (E) | 構成・評価義務 | 指定データ→A–C | 非零H¹、候補判定、G-136回帰 |

安全元一覧、最大元、固定点、比較同型、期待rankを入力fieldに置くと、対応する構成義務が残る。
構成した結果を証拠付き出力にまとめることは許す。

## 完了条件

1. A–Cの一般構成と同値、Bの入力ごとの有限判定、Dの三主張の決着、Eの全指定評価を
   Leanで示す。Dは成立・不成立のいずれも、事前に指定した側の証拠が揃えば達成とする。
   このGOALで証明するtargetは判定定理群全体であり、三主張をすべて真とする命題ではない。
   一つの反例だけで他の未完了条項を閉じない。
2. 成果を `research/lean/ResearchLean/AG/SafeCoarseningOrder/`、条項・実宣言・原始入力・
   判定結果・前提の出所と使用先の対応を `research/reports/G-137-aat-safe-coarsening-order.md` に置く。
   数学的有限構成の証明を求めるもので、DSL・外部API・ArchSigの入力処理実装は成果物に含めない。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従う。DとEで認めた成立判定以外の固定要求が破れた場合は、共通の反証・停止手順で扱う。
   draftの文書作成と、active化後の証明・完了判定を区別する。
