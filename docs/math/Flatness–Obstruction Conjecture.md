## 主定理候補：アーキテクチャ零曲率定理

**Architecture Flatness Theorem / Conjecture AAT-0: Flatness–Obstruction Conjecture**

日本語では、この中心定理候補を **アーキテクチャ零曲率定理** と呼ぶ。

```text
有限な法則宇宙と完全被覆の下で、
アーキテクチャが法則健全であることは、
要求法則族に対する有限な阻害証人が存在しないこと、
すなわち ArchitectureSignature の要求阻害軸がすべて零であることと同値である。
```

この文書は数学面の草案である。Lean 化では最初から数値的な曲率を導入せず、
generic witness-count kernel、可換図式の特殊例、零カウント橋渡しとして形式化する。
詳細は [アーキテクチャ零曲率定理 Lean 化設計](../formal/flatness_obstruction_lean_design.md)
に置く。

有限なアーキテクチャ `A` を、依存グラフ、実行時依存グラフ、具象操作の圏、抽象設計の圏、観測写像、状態遷移代数、effect 代数、境界 policy の組として表す。

```text
A =
  < G_static,
    G_runtime,
    C_concrete,
    C_abstract,
    F : C_concrete → C_abstract,
    Obs,
    StateTransitionAlgebra,
    EffectAlgebra,
    BoundaryPolicy >
```

このとき、設計原則が要求する法則群 `L` から生成される合同関係を `≡_L` とする。たとえば、

```text
f ∘ f ≡ f                         -- idempotency
compensate ∘ action ≡ id           -- compensation
project(xs ++ ys) ≡ replay(project(xs), ys)
decode ∘ encode ≡ id               -- roundtrip
F(g ∘ f) ≡ F(g) ∘ F(f)             -- functorial abstraction
ActualEffects(c) ⊆ AllowedEffects(zone(c))
```

といった法則である。

ここで、実装上の観測意味論 `Sem_A` が、法則で同一視されるべき二つの経路を本当に同じ観測へ写すかを見る。

```text
Curv_A(p, q) = Sem_A(p) - Sem_A(q)
  where p ≡_L q
```

`Curv_A(p, q) = 0` なら、その図式は可換である。
`Curv_A(p, q) ≠ 0` なら、そこにアーキテクチャ欠陥がある。

このとき、次が同値である、という予想です。

```text
A is architecturally lawful
⇔
all required algebraic diagrams commute
⇔
Curv_A = 0
⇔
all obstruction components Ω(A) vanish
⇔
ArchitectureSignature(A) has no measured violation
   and no required unmeasured law under complete coverage
```

より具体的には、以下が同時に成立する。

```text
Ω_dependency(A) = 0
Ω_projection(A) = 0
Ω_observation(A) = 0
Ω_state(A) = 0
Ω_effect(A) = 0
Ω_runtime(A) = 0
```

逆に、どれかの障害成分が非零なら、必ず有限 witness が存在する。

```text
closed dependency walk
or SCC recurrent block
or functoriality square
or LSP / observation counterexample
or retry idempotency counterexample
or compensation counterexample
or replay split counterexample
or roundtrip loss witness
or effect leakage witness
or invariant violation witness
```

これが証明されると、`ArchitectureSignature` は単なる経験的スコアではなく、**アーキテクチャ障害の有限生成された obstruction vector** になります。

---

## 何が「数学的発見」になるか

この予想の発見は、次の一文に圧縮できます。

> アーキテクチャ品質の破れは、代数法則で可換であるべき図式が可換でないこと、すなわちアーキテクチャ曲率である。

これはかなり強いです。

レイヤードアーキテクチャの循環依存は、依存グラフ上の閉路という「経路の戻り」です。
冪等性違反は、`f` と `f ∘ f` の非可換性です。
補償失敗は、`id` と `compensate ∘ action` の非可換性です。
Event Sourcing の replay 失敗は、`project(xs ++ ys)` と `replay(project(xs), ys)` の非可換性です。
DTO roundtrip loss は、`id` と `decode ∘ encode` の非可換性です。
DIP / Clean Architecture の抽象化失敗は、`F(g ∘ f)` と `F(g) ∘ F(f)` の非可換性です。
Effect leakage は、境界 ideal の外へ effect が流出する「境界を横切る flux」です。

つまり、バラバラに見える設計原則が、全部 **「非零曲率を消す操作」** として統一される。

これが代数的アーキテクチャ論の基本定理候補です。

---

## 基本定理候補 1：依存グラフの冪零成分・再帰成分分解予想

文書ではすでに、有限 DAG、walk acyclicity、adjacency matrix nilpotence、`rho(A)=0` の構造的 bridge が中核にあります。ここをさらに大予想にできます。([GitHub][2])

**Conjecture AAT-1: Nilpotent–Recurrent Decomposition Conjecture**

有限依存グラフ `G` の隣接行列 `A` は、成分の並べ替えによって次の形へ分解できる。

```text
A =
[ R1  *   *   * ]
[ 0   R2  *   * ]
[ 0   0   N   * ]
[ 0   0   0   ... ]
```

ここで、

```text
N  = nilpotent part
Ri = recurrent SCC block
```

`N` は有限伝播する健全部分であり、`Ri` は循環的・再帰的な障害核である。

予想のアーキテクチャ的主張は次です。

```text
変更波及の本質的リスクは、
単なる fanout ではなく、
recurrent SCC block の spectral mass によって支配される。
```

有用な指標はこれです。

```text
spectralCyclePressure(A)
  = Σ_i weight(R_i) · ρ(R_i)
```

または最大値版。

```text
maxRecurrentRadius(A)
  = max_i ρ(R_i)
```

これが証明・実証されると、`sccMaxSize` より強い指標になります。

`SCC が大きいから危険` ではなく、

```text
SCC 内部にどれだけ増幅的な再帰構造があるか
```

を測れるようになる。

---

## 基本定理候補 2：伝播 resolvent 予想

**Conjecture AAT-2: Propagation Resolvent Conjecture**

依存辺ごとに「変更が伝播する確率」または「障害が伝播する重み」`p_e` を置く。重み付き隣接行列を `W` とする。

このとき、局所変更が平均してどれだけ広がるかは、

```text
R_p(W) = I + W + W^2 + W^3 + ...
       = (I - W)^(-1)
```

で近似される。ただし `ρ(W) < 1` のとき。

DAG なら `W` は冪零なので、

```text
R_p(W) = I + W + ... + W^k
```

で必ず有限和になる。

一方、`ρ(W) ≥ 1` に近づくほど、変更波及・障害波及は臨界的になる。

有用な指標はこれです。

```text
propagationCriticality = ρ(W)

expectedBlastRadius(i)
  = sum_j ((I - W)^(-1))_{ij}

globalPropagationRisk
  = ||(I - W)^(-1)||_1
```

これは `maxDepth`, `fanoutRisk`, `reachableConeSize`, `rho(A)` を一本につなげます。

大きな発見になるポイントは、循環依存を単に `hasCycle = true` と見るのではなく、

```text
ρ(W) < 1 なら減衰する循環
ρ(W) = 1 なら臨界循環
ρ(W) > 1 なら増幅循環
```

として分類できることです。

つまり、循環は全部同じ悪ではない。
**増幅する循環が悪い。**

---

## 基本定理候補 3：抽象化曲率予想

PRD では projection / functor soundness として、`F(id)=id`, `F(g ∘ f)=F(g) ∘ F(f)` を測る方向が書かれています。ここから非常に美しい予想が作れます。([GitHub][3])

**Conjecture AAT-3: Abstraction Curvature Conjecture**

具象アーキテクチャの操作圏を `C`、抽象アーキテクチャの操作圏を `B`、抽象射影を `F : C → B` とする。

抽象化曲率を次で定義する。

```text
K_F(f, g)
  = F(g ∘ f) - F(g) ∘ F(f)
```

このとき、

```text
K_F = 0
⇔
抽象設計は具象実装の合成構造を正しく表現している
```

逆に `K_F(f,g) ≠ 0` なら、

```text
具象実装では一つの workflow として成立しているものが、
抽象設計上の合成としては嘘になっている。
```

有用な指標はこれです。

```text
abstractionCurvatureCount
compositionPreservationViolation
identityPreservationViolation
projectionAmbiguityCount
projectionCompletenessGap
```

これは DIP や Clean Architecture の理論的中核になり得ます。

Clean Architecture の本質は、

```text
依存方向が綺麗であること
```

ではなく、

```text
具象 workflow が抽象 workflow として functorial に読めること
```

だと言えるようになる。

---

## 基本定理候補 4：観測核による LSP 完全性予想

文書では observation factorization と LSP-compatible な構造がすでに出ています。これをさらに明確に定理候補化できます。([GitHub][2])

**Conjecture AAT-4: Observation Kernel Conjecture**

抽象射影を `F : Impl → Abs`、観測を `Obs : Impl → O` とする。

実装 `x, y` が同じ抽象へ写るとき、

```text
F(x) = F(y)
```

それらが常に同じ観測を持つなら、

```text
Obs(x) = Obs(y)
```

置換可能性が成立する。

つまり、

```text
ker(F) ⊆ ker(Obs)
```

が LSP の代数的条件である。

この予想が証明されると、LSP を自然言語の設計原則ではなく、

```text
抽象射影の核が観測の核に含まれるか
```

という測定可能な条件にできます。

有用な指標はこれです。

```text
observationalKernelDefect
  = |{ (x, y) |
        F(x) = F(y)
        but Obs(x) ≠ Obs(y) }|

behavioralDistanceWithinFiber
  = Σ over fibers F^{-1}(a) of pairwise observational divergence
```

これは `lspViolationCount` より一段強いです。
`同じ interface を実装しているのに振る舞いが違う` を、fiber 内の観測不一致として測れるからです。

---

## 基本定理候補 5：状態遷移代数の confluence 予想

PRD では Event Sourcing、Saga、冪等性、補償、roundtrip、invariant preservation が個別 law として整理されています。ここをさらに統一するには、状態遷移を「生成元と関係式を持つ代数」として見るのがよいです。([GitHub][3])

**Conjecture AAT-5: State Transition Confluence Conjecture**

コマンド、イベント、補償、リトライ、スナップショット、migration を、状態遷移代数の生成元とする。

```text
Generators:
  commands
  events
  compensations
  retries
  snapshots
  migrations

Relations:
  f ∘ f = f
  comp ∘ f ≈ id
  project(xs ++ ys) = replay(project(xs), ys)
  decode ∘ encode ≈ id
  migrate ∘ project_old = project_new ∘ migrateEvents
```

このとき、観測同値 `≈_Obs` の下で rewrite system が局所合流的なら、

```text
任意の履歴は一意な観測正規形を持つ。
```

つまり、

```text
履歴再構成性
補償整合性
retry safety
snapshot consistency
migration naturality
```

が、ひとつの confluence 条件に統一される。

有用な指標はこれです。

```text
criticalPairDefectCount
normalFormAmbiguity
historyHolonomy
replayHomomorphismDefect
compensationDefectCount
idempotencyViolationCount
snapshotRoundtripDefect
eventMigrationNaturalityDefect
```

特に `historyHolonomy` は強い指標になります。

```text
historyHolonomy(h1, h2)
  = Obs(eval(h1)) - Obs(eval(h2))
  where h1 ≡_L h2
```

これは、「同じ意味であるべき二つの履歴が、違う観測結果へ到達する」量です。

---

## 基本定理候補 6：effect 境界 ideal 予想

PRD の effect leakage は、依存グラフでは見えない重要軸です。ここは effect algebra / quantale として扱うと強くなります。([GitHub][3])

**Conjecture AAT-6: Effect Ideal Boundary Conjecture**

各 zone に許可 effect 集合を割り当てる。

```text
AllowedEffects : Zone → Set Effect
```

ただの集合ではなく、各 `AllowedEffects(z)` は effect algebra の ideal であるとする。

```text
e ∈ AllowedEffects(z)
and e ≤ e'
does not automatically imply e' allowed

but

allowed effects are closed under
safe composition,
safe weakening,
declared handlers.
```

このとき、境界が健全であることは、

```text
ActualEffects(component)
  ⊆ AllowedEffects(zone(component))
```

が全 component で成立することと同値である。

さらに、handler coverage を含めると、

```text
∀ e ∈ ActualEffects(c), ∃ h, Handles(h, e)
```

が必要になる。

有用な指標はこれです。

```text
effectFlux
  = Σ_c | ActualEffects(c) \ AllowedEffects(zone(c)) |

ambientAuthorityIndex
  = count(global env / implicit IO / default credential usage)

handlerDefect
  = |{ e | e is actual but no handler exists }|

nonCommutingEffectPairCount
  = |{ (e1, e2) |
        declared commuting
        but e1 ; e2 ≠ e2 ; e1 }|
```

この予想が強いのは、Clean Architecture を import graph だけでなく、

```text
許可されない effect が境界を横切っていないか
```

として定式化できるところです。

---

## 基本定理候補 7：Architecture Signature の普遍性予想

最後に、最も抽象的だがインパクトの大きい予想です。

**Conjecture AAT-7: Universality of Architecture Signature**

`ArchitectureSignature` は、任意に選んだメトリクス集ではない。
それは、宣言された law universe `L` に対して、有限観測可能なアーキテクチャ欠陥を記録する **自由な多軸不変量** である。

形式的には、次の性質を満たす任意のリスク評価 `M` を考える。

```text
1. law-preserving refactoring に対して単調
2. disjoint union に対して加法的
3. measured zero と unmeasured を区別する
4. counterexample witness を持つ violation を非零に写す
5. law universe の変更に対して比較不能性を保存する
```

このとき、`M` は `ArchitectureSignature` を通して因子化する。

```text
          Sig
Arch_L --------> RiskVector_L
  \                 |
   \ M              | φ
    \               v
     ----------> OtherMetric
```

つまり、

```text
M = φ ∘ Sig
```

となる単調写像 `φ` が存在する。

これが証明されると、`ArchitectureSignature` の地位が変わります。

今は、

```text
便利な多軸メトリクス
```

ですが、証明後は、

```text
law universe に対する普遍的な欠陥測度
```

になります。

これは基本定理級です。

---

## 最も推したい中心命題

論文・研究ノートの中心に置く定理候補はこれです。

```text
アーキテクチャ零曲率定理

有限アーキテクチャ A と法則宇宙 L に対して、
完全被覆があるなら、
A が L に関して法則健全であることは、
要求法則族に対する有限な阻害証人が存在しないことと同値である。

可換図式の非可換性は、その最重要な特殊例である。
ArchitectureSignature は、その阻害証人族の多軸座標表示である。
```

日本語で言うなら、

> アーキテクチャの破れとは、要求法則族に対する有限な阻害証人が現れることである。
> Architecture Signature とは、その阻害証人族の座標表示である。

これが一番強いと思います。

---

## この予想から導かれる新しい指標

既存指標に加えて、次の指標群を入れると「数学的発見」感が出ます。

| 指標                          | 意味                                  |
| --------------------------- | ----------------------------------- |
| `architectureCurvature`     | 可換であるべき図式の非可換量の総和                   |
| `obstructionRank`           | 独立な obstruction witness の最小生成数      |
| `spectralCyclePressure`     | recurrent SCC block の spectral mass |
| `propagationCriticality`    | `ρ(W)`、伝播が減衰するか増幅するか                |
| `resolventPropagationRisk`  | `(I-W)^(-1)` による期待波及量               |
| `abstractionCurvatureCount` | `F(g∘f) ≠ F(g)∘F(f)` の件数            |
| `observationalKernelDefect` | `ker(F) ⊆ ker(Obs)` の破れ             |
| `historyHolonomy`           | 同値な履歴が異なる観測へ行く量                     |
| `effectFlux`                | zone 境界を越えて漏れた effect 量             |
| `normalFormAmbiguity`       | 状態遷移履歴の正規形が一意でない度合い                 |
| `repairRank`                | 全 obstruction を消すのに必要な最小修正単位数       |

特に推したいのはこの5つです。

```text
architectureCurvature
obstructionRank
spectralCyclePressure
observationalKernelDefect
historyHolonomy
```

この5つは、単なる実務メトリクスではなく、理論の顔になります。

---

## 研究上の勝ち筋

この方向で進めるなら、最初の論文・technical note の主張はこうできます。

1. 依存グラフ層では、層化可能性・非循環性・有限伝播・隣接行列の冪零性が同じ現象の別表現である。
2. 代数法則層では、冪等性・補償・replay・roundtrip・projection・effect policy は、すべて可換図式として表せる。
3. アーキテクチャ欠陥は、それらの図式の非可換性、すなわち obstruction である。
4. `ArchitectureSignature` は obstruction の座標表示である。
5. 実コード上の診断は、各 obstruction の witness を抽出する問題である。

この形にすると、「アーキテクチャレビューを感想から診断へ」というゴールに対して、単なるツールではなく、

```text
診断とは obstruction witness の提示である
```

という数学的定義を与えられます。

これが代数的アーキテクチャ論の基本定理候補として、最もインパクトが大きいと思います。
