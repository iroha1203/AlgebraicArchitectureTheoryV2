# Part 3: Architecture Dynamics / Chaos Game 編

## 1. 力学編の目的

基礎編と発展編では、feature extension と operation を個別に扱った。
力学編では、operation が反復されるとき、architecture がどのような signature trajectory を
描くかを扱う。

中心命題は次である。

```text
architecture
  = future operation distribution を曲げる field

software quality
  = signature trajectory の安定性と方向
```

この立場では、良い architecture は snapshot として整っているだけではない。
将来の変更を、よい invariant が保存されやすい領域へ誘導し、悪い obstruction が増える
方向を減衰する。

## 2. Architecture Configuration と Observation

力学編では、architecture を反復操作の対象として見る。

```text
configuration X
observation sigma = Obs(X)
```

`Obs` は、多軸 signature、選択された invariant family、または特定の obstruction measure を
返す観測である。異なる observation を選べば、同じ configuration でも違う力学が見える。

## 3. Operation Distribution

開発は、可能な operation の集合から一つずつ選ばれる反復過程として読める。

```text
X_{t+1} = op_t(X_t)
```

ここで `op_t` は、要求、設計、既存構造、開発者の慣習、自動生成、レビュー、制約により
選ばれやすさが変わる。

```text
P(operation | architecture context)
```

この確率分布は、観測や経験から読むための表現であり、AAT の形式的な核そのものではない。
形式側の核は、有限または bounded な operation support、bounded operation script、
accepted transition predicate、明示された preservation assumption である。

```text
formal core:
  finite operation support
  + bounded script
  + accepted transition
  + explicit preservation assumptions

probabilistic reading:
  weights over the selected support
```

この境界により、確率重みを持つ reading と、有限 support 上の保存性主張を混同しない。

この分布は固定ではない。architecture 自身が、未来に選ばれやすい operation を変える。
よい境界、明確な型、良い canonical example は、良い operation を選びやすくする。
不明瞭な責務、巨大な共通 module、曖昧な service は、悪い operation を選びやすくする。

## 4. Codebase as Prompt

コードベースは、未来の変更に対する暗黙の prompt として働く。

周辺コード、名前、型、例外処理、テスト粒度、層構造、既存の shortcut は、次の変更が
どこへ足され、どの抽象を通り、どの境界を無視しやすいかを決める。

```text
architecture quality
  ~= quality of the local grammar induced for future patches
```

この観点では、architecture は repository-scale prompt engineering でもある。
良い canonical example は seed attractor として働き、悪い exemplar は悪い basin を
深くする。

coupon feature extension では、coupon calculation が declared interface を通る例が seed
attractor になる。逆に、coupon service が payment adapter や hidden cache を直接読む例は、
将来の変更を同じ shortcut へ誘導する bad exemplar になる。

## 5. Signature Trajectory

signature trajectory は、operation sequence に沿った observation の列である。

```text
sigma_0, sigma_1, ..., sigma_n
```

各 step には delta がある。

```text
Delta_t = sigma_{t+1} - sigma_t
```

net delta は、trajectory 全体の endpoint 差を読む。

```text
NetDelta = Delta_0 + ... + Delta_{n-1}
```

ただし endpoint がよいだけでは、途中の trajectory がよいとは限らない。
一度大きく悪い領域へ入り、その後戻る path と、ずっと安全領域に留まる path は異なる。

## 6. Safe Region

safe region は、選ばれた signature や invariant measure が許容範囲にある領域である。

```text
SafeRegion sigma
```

operation が safe region を保存するとは、入力が safe region にあるとき、出力も safe
region にあることを意味する。

```text
StepPreservesSafeRegion op :=
  SafeRegion sigma(X) -> SafeRegion sigma(op X)
```

safe endpoint だけでは path safety は従わない。path safety には、各 step が safe region を
保存すること、または trajectory 全体が selected safe region 内にあることが必要である。

## 7. Attractor と Basin

attractor は、反復操作により trajectory が滞留しやすい signature 領域である。
basin は、その attractor へ落ちやすい初期 configuration の集合である。

```text
Attractor :=
  recurrent signature region
  + stability condition
  + observation boundary

Basin :=
  initial configurations that reach the attractor region
```

技術的負債は、悪い signature 領域へ吸引する basin として読める。
良い architecture は、良い attractor を作るだけでなく、悪い attractor からの escape cost を
下げる。

## 8. Chaos-game Reading

chaos game 的な読みでは、複数の operation family が確率的または選択的に反復される。

```text
choose op_i from operation support
apply op_i
observe sigma
repeat
```

operation support は、選ばれうる operation の有限または bounded な集合である。

```text
OperationSupport(X) = { op_1, ..., op_k }
```

support がよく設計されていれば、どの operation が選ばれても target region に留まりやすい。
support に有害な operation が含まれていれば、accepted step が局所的に安全でも、未来の
trajectory が悪い方向へ分岐しうる。

## 9. Support Shaping

support shaping は、未来に選ばれうる operation の集合を変える設計操作である。

```text
support shaping :=
  remove bad operation
  + add good operation
  + make lawful path easier
  + make unlawful shortcut harder
```

refactoring は、その時点の構造を整理するだけではない。未来の operation distribution を変える
basin reshaping として読む。

```text
refactoring
  = architecture field transformation
  = operation distribution transformation
```

## 10. Constraint と Attractor Engineering

constraint は、出てきた operation を拒否、射影、減衰、修正する。
Attractor Engineering は、そもそも良い operation が自然に選ばれやすい field を作る。

```text
constraint:
  raw operation -> accepted / rejected / projected operation

attractor engineering:
  architecture field -> operation support itself
```

したがって、accepted operation が安全領域を保存することと、operation support 全体が
安全領域を保存することは異なる。良い architecture は、悪い operation を外から止めるだけでなく、
悪い operation が局所最適にならない構造を持つ。

## 11. Debt Potential Well

技術的負債は、悪い attractor / basin だけでなく、potential well としても読める。
短期的に便利な場所には、変更が落ち込みやすい。

```text
common module
global context
shared helper
legacy adapter
base service
implicit configuration
```

これらは局所的には合理的な追加先である。しかし反復されると、hidden dependency、
responsibility leakage、effect leakage、semantic coupling を蓄積する。

悪い attractor は深い井戸であり、escape cost はそこから抜けるために必要な repair /
refactor energy として読める。

```text
debt potential well
  = region where local optimization repeatedly increases global obstruction
```

## 12. Local Correctness Trap

Local Correctness Trap とは、各 step は局所的には正しいが、反復により global invariant が
劣化する現象である。

典型的には次の形を取る。

```text
step 1: local special case
step 2: another local special case
step 3: shared flag
step 4: global helper
step 5: hidden dependency
```

各 step は局所仕様を満たす。しかし trajectory 全体では、dependency、semantic alignment、
runtime exposure、boundary policy が悪化する。

AAT では、この罠を single-step correctness と trajectory-level invariant preservation の
差として読む。

## 13. Change Force

変更は、単なる差分ではなく、signature 空間上の force として読める。

```text
change force
  = Delta signature induced by an accepted architecture transition
```

force は単一成分ではない。

```text
feature force
repair force
coupling force
boundary force
invariant force
effect force
debt force
refactor force
```

良い変更は、feature force と stabilizing force を同時に持つ。

```text
v = v_feature + v_stabilize
```

悪い変更は、局所的な feature force と小さな debt force を同時に持ち、その小さな力が
反復で蓄積する。

```text
v = v_feature + v_debt
```

複数の変更 force は単純な和として読める場合もあるが、operation は一般に非可換なので、
適用順序により合力の意味は変わる。

## 14. Merge-order Sensitivity

operation は一般に可換ではない。

```text
op_a ; op_b
  !=
op_b ; op_a
```

二つの operation がどちらも局所的に lawful でも、順序により最終 observation が異なることが
ある。この差は merge-order sensitivity として読む。

距離付き observation を持つ場合、operation commutator curvature として、順序差の大きさを
数値化できる。

```text
curvature(op_a, op_b, X)
  = distance(Obs(op_b(op_a(X))), Obs(op_a(op_b(X))))
```

この値は経験的リスクそのものではない。あくまで選ばれた observation と distance に
相対化された order sensitivity である。

## 15. Trajectory Shape

signature trajectory は、endpoint だけでなく形状を持つ。

| 軌道形状 | 意味 |
| --- | --- |
| stable orbit | 小変更後も安全領域に戻る。 |
| drift | ゆっくり悪い領域へずれる。 |
| spiral debt | 短期的には戻るが、長期的には悪い basin に近づく。 |
| phase shift | ある操作を境に signature が急変する。 |
| oscillation | feature addition と repair が周期的に良悪を往復する。 |
| scatter | 近い操作列から大きく異なる trajectory が出る。 |
| basin capture | ある時点から特定の悪い構造に吸着される。 |

この分類は、単一 snapshot や endpoint delta では見えない。AAT Dynamics は、trajectory を
first-class object として扱う。

## 16. Observability Expansion Shock

observation が粗いと、ある trajectory は安全に見える。しかし observation を細かくすると、
隠れていた軸が nonzero になることがある。

```text
coarse observation:
  safe

refined observation:
  hidden obstruction appears
```

これを observability expansion shock と呼ぶ。

粗い observation で安全であることから、 refined observation でも安全であることは従わない。
この境界は、未観測軸を zero と読まないという AAT の基本方針と同じである。

## 17. Damping と Control

review、type discipline、architecture rules、tests、design constraints は、悪い operation を
拒否または減衰する control input として読める。

```text
raw operation distribution
  -> control / damping
  -> accepted operation distribution
```

damping が十分なら、bad-axis measure は非増加または減少する。
ただし damping の効果は明示的な仮定であり、operation が accepted されたという事実だけから
bad-axis nonincrease は従わない。

## 18. Architecture Dynamics の中心式

力学編の最小閉ループは次である。

```text
architecture field
  -> operation distribution
  -> accepted / rejected transitions
  -> signature trajectory
  -> updated architecture field
```

この loop により、architecture quality は snapshot の性質だけでなく、future operation
distribution と trajectory の性質として読める。

## 19. 力学編の境界

Architecture Dynamics / Chaos Game 編は、次を主張しない。

```text
- same signature から same future operation support が従う。
- safe endpoint から safe trajectory が従う。
- axis-wise safety から global safety が従う。
- accepted step から bad-axis nonincrease が無条件に従う。
- coarse observation safety から refined observation safety が従う。
- curvature value から経験的リスクが無条件に従う。
- finite attractor candidate から global attractor が従う。
```

力学編の役割は、architecture を未来の変更分布を曲げる field として読み、
quality を signature trajectory、attractor、basin、support shaping の語彙で扱うことである。
