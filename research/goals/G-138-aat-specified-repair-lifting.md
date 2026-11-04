# G-138-aat-specified-repair-lifting — 指定補正の持ち上げ障害と全解の分類

- `id`: `G-138-aat-specified-repair-lifting`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6191](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6191)
- `source note`: [n1016 §4.8・候補18](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [構成と証明方針](../designs/G-138-aat-specified-repair-lifting/README.md)、[実比較への接続と有限構成](../designs/G-138-aat-specified-repair-lifting/connections-and-computation.md)、[指定例](../designs/G-138-aat-specified-repair-lifting/witnesses.md)、[再利用対応](../designs/G-138-aat-specified-repair-lifting/reuse-map.md)

## 研究目的

診断側で指定した補正を、元の側で同じ値を保って実現できる条件と、その全解を求める。
G-125は有理診断の零性から整数補正を構成し、G-133は標準写像錐と比較の欠損を扱う。
本目標では両者を、指定補正そのものに対する障害類、解集合、残る自由度へ接続する。

一般アーベル群の定理、同じAAT実比較への適用、有限表示整数入力からの判定を一体で扱う。
補正の存在、指定補正の持ち上げ、持ち上げの一意性を別々の結論として証明する。

問題設定は、cochain写像に沿う指定元の持ち上げと、その障害・全解という数学的問いから定める。
一般性は任意のアーベル群の複体で保持し、有限表示の場合の有効構成をその特殊化として証明する。
AATの実比較への適用も、既存の係数層と比較写像から導く。

## 固定target

T0・A–E・Wを一つの定理群とする。参照設計の式と指定例も固定要求に含める。

### T0. 入力、量化、等号

任意の非負次数のアーベル群のcochain複体C、D、任意のcochain写像φ:C→Dを取る。
各群に有限性・自由性・無torsion性を課さず、高次数の項と微分を許す。
負次数へ零延長し、標準写像錐を整数次数で扱う。
これらを固定した後、すべてのz∈Z¹(C)、b∈D⁰でd_D b=φ¹zを満たすものを量化する。

Liftφ(z,b)={a∈C⁰ | d_C a=z ∧ φ⁰a=b} とする。
等号はcochainの等号であり、cohomology、同型類、更新後状態の商による一致へ変更しない。
元の補正a₀の存在はBの条件付き記述だけで使い、Aには仮定しない。

### A. 標準写像錐による持ち上げ判定

Cone(φ)ⁿ=Dⁿ⊕Cⁿ⁺¹、d(b,c)=(d_D b+φc,−d_C c) の成分規約を
mathlibの標準mapping coneへ同定する。特にCone(φ)⁻¹≅C⁰を保持する。
同じz,bからcocycle (b,−z) とoφ(z,b)∈H⁰(Cone φ)を構成し、

```math
o_\phi(z,b)=0\quad\Longleftrightarrow\quad\operatorname{Nonempty}\operatorname{Lift}_\phi(z,b)
```

を両方向に証明する。零性の証人と持ち上げaを相互に復元する。

### B. 余核障害、選択独立性、全解

kφ:Z⁰(C)→Z⁰(D)をφ⁰から構成する。
d_C a₀=zとなる任意のa₀について、b−φ⁰a₀がZ⁰(D)に属することを証明し、
そのcoker kφでの類がa₀によらないことを示す。
標準錐の実写像から完全列

```math
0\longrightarrow\operatorname{coker}k_\phi
 \xrightarrow{j}H^0(\operatorname{Cone}\phi)
 \xrightarrow{p}\ker H^1(\phi)\longrightarrow0
```

を構成し、j[b−φ⁰a₀]=oφ(z,b)、p(oφ(z,b))=−[z]を証明する。
指定補正の持ち上げを一つa*選べる場合、ker kφの加法による作用を構成し、
任意の二解の差を一意な作用元として回収する。実際のLift全体へAddTorsorを与え、
ker kφ→Liftφ(z,b)、h↦a*+hの両方向同値を構成する。

固定φについて、次を量化を省略せず証明する。

- kφの全射性と「元の補正が存在する全zについて、すべての適合bが持ち上がる」は同値。
- kφの単射性と「すべての適合z,bについてLiftφ(z,b)は高々一元」は同値。
- 非空なLiftについて、その一意性とker kφ=0は同値。

空なLiftをtorsorとして扱わず、全射性の対象を既知の像へ狭めない。

### C. 比較の可換正方形と表示変更

任意のcochain写像α:C→C′、β:D→D′、φ′:C′→D′でβφ=φ′αを満たすものに対し、
a↦α⁰aによるLiftφ(z,b)→Liftφ′(α¹z,β⁰b)を構成する。
同じ平方の錐写像がoφ(z,b)を対応する障害へ送り、kの核・余核の誘導写像、j,p、
解への作用と可換になることを証明する。恒等・合成も保つ。
α,βがcochain同型なら、解集合・障害・作用の同値を構成する。
一般の平方では零性の保存を示し、反映や解の全射性を無条件には要求しない。

### D. G-125の同じ実比較への適用

G-125の `GeneratorPresentation`、`FaceEmptyAATCechCover`、adequate Law、
`ActualCechAffineLocalData` の全入力について、元の `faceEmptyCechComplex`、
独立に作られた `lawGeneratedComplex` と `actualCechCoefficientCochainMap` を
共通のアーベル群の複体へ接続する。零延長・必要な忘却とcochain同定を構成し、
元のAdditiveCechH1、診断H¹、`actualCechDiagnosticH1Map`への可換図式を証明する。

元のactualMismatchをz、任意の診断cochain補正をbとしてA・Bを適用する。
さらにG-125の `CommonLabelChartSupport` と `ReflectionCondition` を満たす入力では、
既存 `integralCorrection` をa₀に取り、同じ実φ⁰によるb−φ⁰a₀を余核障害へ同定する。
床関数が与える補正と、指定bを厳密に実現する補正を区別する。
各持ち上げaによる元の局所状態の更新−aが、元のactualMismatchを零にすることも証明する。
G-125のreading変更について、既存の次数0・1の射をCの平方へ接続し、
同じ入力・同じ指定補正の障害と解の輸送を証明する。

### E. 有限表示整数入力からの判定と復元

C⁰,C¹,C²,D⁰,D¹,D²を有限整数生成元・関係行列で表示し、微分とφの行列、
z,bの代表を与える。行列が商上の射・複体・cochain写像を定め、z,bがT0を満たす条件を
有限検査し、成立時にA・Bの対象へdecodeする。torsionと零個の生成元・関係を含む。

原始整数行列から停止する算法でLiftの空非空、特解、ker kφの有限表示とその全解への作用、
一意性を計算する。非空時は全解の有限表示と元C⁰への復元、空の場合は整数の整除違反または
零行矛盾の検査可能な証拠を返す。返した表示・判定がA・Bの同じLift・障害・作用と一致し、
解の代表変更と関係の商を正しく扱うことをLeanで証明する。
整数消去の結果や解集合を外部の正しい入力として受け取るだけでは算法の構成義務を満たさない。

### W. 指定例と同時成立条件

[指定例W1–W6](../designs/G-138-aat-specified-repair-lifting/witnesses.md)の入力を保持してA–Eへ適用する。
W1の整数→有理の非零余核障害と実G-125への実現、W2の無限な全解、W3の非自明なtorsion、
W4の元の補正の不存在、W5の非零d¹、W6の補正とパラメータ表示の一意性の差を証明する。
Eの算法評価はW2–W5の有限表示整数入力で行い、W1の有理群を有限生成整数群に置き換えない。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 非負複体C,D、cochain写像φ、適合z,b | 入力として保持 | T0。Wでは明示した群・射から条件を証明 | A–C |
| a₀とd_Ca₀=z | Bの方向仮定 | Dのreflection適用では既存integralCorrectionから放電 | 余核障害と全射性 |
| 標準錐、元のcohomologyへの同定、j,pと完全性 | 構成・証明義務 | 標準mapping coneの符号・次数と実商写像 | A・B |
| ker kφの作用・全解同値・一意性 | 構成・証明義務 | 解の差と加法から生成 | B・C・E |
| 可換平方、同型の条件 | Cの一般入力・方向仮定 | Dの適用では元のreading射と可換性から生成 | 自然性・同値 |
| G-125の入力条件・reflection条件 | Dの明示入力 | 既存型の同じ前提。W1では原始入力から放電 | 実比較・床補正 |
| 同じ実比較の零延長・H¹・reading接続 | 構成・証明義務 | 既存次数別射と微分から生成 | D |
| 有限整数表示・行列・代表 | Eの入力 | 整数表。商・複体・適合条件は有限検査から生成 | E・W |
| 停止算法、全解表示、不能証拠 | 構成・証明義務 | 原始行列から生成し、停止・正当性・完全性を証明 | E |
| W1–W6 | 構成・証明義務 | 固定表と一般定理の同じ経路 | 非空虚性・弱化検出 |

## 完了条件

1. T0・A–E・Wを全方向・全量化でLeanに構成する。一般理論、実比較との接続、
   整数算法のいずれかだけで全目標を完了としない。
2. 成果は `research/lean/ResearchLean/AG/SpecifiedRepairLifting/`、固定条項と宣言・
   前提の生成使用・指定例・検証の対応は `research/reports/G-138-aat-specified-repair-lifting.md` に置く。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従う。対象を有理ベクトル空間・free群・零d¹・選んだ補正の像へ縮小する変更、
   cochain一致を類の一致へ変える変更は固定targetの弱化である。
   固定主張への反例は反証として記録し、仮定追加・量化縮小・指定例の変更は人間の判断を要する。
