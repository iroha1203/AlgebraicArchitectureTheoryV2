# AAT 数学理論

この文書は、AAT の数学的核を整理する。実装済み API、Issue、PR、tooling artifact、
empirical pilot の状態はここに混ぜず、[Lean 定義・定理索引](lean_theorem_index.md) と
[証明義務と実証仮説](proof_obligations.md) へ分離する。

## 1. 中心命題

AAT は、ソフトウェア開発を単なるコード差分ではなく、architecture の拡大、操作、
不変量、obstruction、証明義務、証明書の理論として扱う。

```text
software architecture change
  = architecture extension
  + architecture operation
  + invariant family
  + obstruction witness
  + proof obligation
  + certificate
```

設計レビューの問いは、主観的な良否ではなく次の形になる。

```text
既存 core は拡大後にも保存されているか。
feature は selected universe 上で split するか。
相互作用は declared interface を通るか。
どの invariant が保存され、どの invariant が破れたか。
split しないなら、どの obstruction witness がそれを説明するか。
どの theorem precondition が満たされ、どの non-conclusion が残るか。
```

## 2. Architecture Object

AAT の対象は、実コードベースそのものではない。実コード、仕様、レビュー、運用観測から
切り出された、理論が扱える bounded な architecture object である。

```text
ArchitectureObject :=
  components
  + static dependency relation
  + runtime dependency relation
  + boundary policy
  + abstraction policy
  + observation model
  + semantic diagram universe
```

`ComponentUniverse` は proof-carrying measurement universe である。
selected components、selected relations、coverage boundary、exactness boundary を保持し、
universe 外の component や relation について zero を主張しない。

`ComponentCategory` は reachability を Hom とする thin category として読む。
path count や walk length は忘れる。定量指標は `Walk`, `Path`, finite metrics,
adjacency matrix, または別 representation 側で扱う。

`Decomposable` は現在 `StrictLayered` として読む。acyclicity、finite propagation、
nilpotence、spectral condition は定義に混ぜず、別 theorem または proof obligation として
接続する。

## 3. Feature Extension

機能追加は、既存 architecture を保ったまま拡大 architecture へ移る操作である。

```text
FeatureExtension :=
  core graph
  + feature graph
  + extended graph
  + core embedding
  + feature embedding
  + feature view / observation
  + declared interface
```

良い feature extension は、既存 core を壊さず、新機能差分を説明可能な形で取り出せる。
ただし、AAT は split claim を一つの万能 package にしない。

```text
FeatureExtension
  = core embedding と feature view を持つ拡大

StaticSplitFeatureExtension
  = static relation と boundary policy に関する split evidence

SplitExtensionLiftingData
  = feature step が declared interface を通って持ち上がるための evidence

SplitFeatureExtensionWithin
  = universe、observation、invariant family に相対化された split claim
```

static split が成り立っても、runtime protection や semantic diagram filling は別前提を
必要とする。

## 4. Invariant と Law Universe

`Invariant` は architecture object や operation が保存すべき性質である。

```text
dependency direction
boundary policy
abstraction policy
observation equivalence
local contract
replay law
compensation law
runtime protection
convergence condition
```

`LawUniverse` は、required laws、optional laws、derived laws、witness family、
observation boundary を束ねる。

lawfulness は obstruction absence と同じものとして最初から定義しない。
まず意味論的な `Lawful` predicate を置き、finite witness family と signature axes を通じて
接続する。

```text
lawfulness
  <-> no required obstruction witness
  <-> required signature axes are available and zero
```

この読みは、universe、coverage、exactness、observation boundary に相対化される。
未観測軸や対象外の law を zero と読まない。

## 5. Obstruction Witness

`ObstructionWitness` は、望ましい性質が成り立たない理由を構造的に示す対象である。

```text
forbidden static edge
hidden interaction
boundary policy violation
abstraction leakage
non-commuting semantic diagram
runtime exposure
lifting failure
filling failure
complexity transfer
residual coverage gap
```

obstruction は単なるエラーではない。修復、分類、不能性証明、進化軌道の変化を説明する
witness である。

有限 witness universe 上では、zero-count kernel が最小核になる。

```text
violatingWitnesses bad xs :=
  xs filtered by bad

violationCount bad xs :=
  length (violatingWitnesses bad xs)

violationCount bad xs = 0
  <-> every measured witness is not bad
```

## 6. Architecture Signature

`ArchitectureSignature` は単一スコアではなく、多軸診断である。
複数の invariant や obstruction family を軸ごとに読む。

```text
ArchitectureSignature :=
  static axes
  + boundary axes
  + abstraction axes
  + extension axes
  + runtime axes
  + semantic axes
  + evolution axes
```

より強く言えば、signature は selected obstruction families の座標表示である。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

各軸は measurement status を持つ。`none` や `unmeasured` は risk 0 ではない。
測定済み 0、未測定、対象外、private / unavailable evidence を混同しない。

## 7. Proof Obligation と Certificate

`ProofObligation` は、operation や theorem package が要求する前提と結論を明示する。

```text
ProofObligation :=
  formal universe
  + required laws
  + invariant family
  + witness universe
  + coverage assumptions
  + exactness assumptions
  + operation preconditions
  + conclusion
  + non-conclusions
```

`Certificate` は、claim がどの universe、どの evidence、どの observation、
どの non-conclusion に依存するかを記録する。

```text
CertifiedArchitecture :=
  architecture
  + claims
  + evidence boundary
  + measurement boundary
  + non-conclusions
```

`nonConclusions` は必須である。static split から runtime flatness や semantic flatness は
自動的には従わない。selected universe で obstruction が見つからなくても、
全 universe で obstruction が存在しないとは限らない。

## 8. Architecture Calculus

`ArchitectureOperation` は、architecture object を別の architecture object へ写す操作である。

```text
compose
replace
refine
abstract
split
merge
isolate
protect
migrate
reverse
contract
repair
synthesize
```

operation は tag だけでは theorem を持たない。各 operation は、前提、不変量、
witness mapping、結論、non-conclusion を持つ proof obligation を生成する。

```text
operation
  -> proof obligation
  -> required assumptions
  -> selected conclusion
```

calculus law も無条件ではない。identity、composition、associativity under observation、
projection compatibility、repair monotonicity、synthesis soundness などは、どの observation、
interface、witness universe、exactness assumption に相対化して成立するかを持つ。

## 9. Operation と Invariant の対応

AAT では、operation family と invariant family の間に弱いガロア的対応を見る。

```text
Ops(I) = invariant family I を保存する operation の集合
Inv(O) = operation family O によって保存される invariant の集合
```

より強い invariant family を要求すれば許される operation は減り、より多くの operation を
許せば保存される invariant は減る。

設計パターンは自然言語の標語ではなく、operation family、invariant family、closure law、
non-conclusions を持つ package として扱う。

## 10. Repair と Synthesis

repair は selected obstruction を減らすための operation である。

```text
RepairStep :=
  source
  + target
  + selected obstruction measure
  + decrease proof obligation
  + side-effect boundary
```

repair は総合的改善を意味しない。ある selected obstruction が減っても、
別の軸へ complexity が転送されることがある。

synthesis は、制約を満たす architecture object または operation sequence を構成する問題である。
解がある場合は candidate certificate を持ち、解がない場合は `NoSolutionCertificate` が
候補 universe と制約の下での不能性を説明する。

## 11. Path, Homotopy, Diagram Filling

`ArchitecturePath` は operation sequence である。

```text
X0 -> X1 -> X2 -> ... -> Xn
```

異なる path が同じ feature outcome に到達しても、途中で保存される invariant、
導入される obstruction、観測される signature trajectory は異なりうる。

`PathHomotopy` は、選ばれた generator と observation model のもとで、二つの path が同じ
観測を与えることを扱う bounded skeleton である。

semantic diagram は、異なる実装経路や操作順序が同じ observation を与えることを表す。
diagram filler はこの同値性を支える証拠であり、観測差は non-fillability witness になる。

```text
Obs(lhs) != Obs(rhs)
  -> NonFillabilityWitness D
```

## 12. Graph, Matrix, Propagation

有限 unweighted universe 上では、acyclicity、closed walk absence、adjacency nilpotence は
同じ構造を異なる表示で読む。

```text
finite unweighted universe:

acyclic
  <-> no closed walk
  <-> nilpotent adjacency matrix
```

finite propagation、runtime exposure、weighted spectral reading は別物である。
unweighted theorem、bounded propagation reading、weighted spectral reading を混同しない。

## 13. State Transition Algebra と Effect Boundary

状態遷移層では、command、event、retry、compensation、snapshot、migration を生成元として
扱い、それらの law を関係式として読む。

```text
f ; f = f
compensate ; action ~= id
project(xs ++ ys) = replay(project(xs), ys)
decode ; encode ~= id
migrate ; project_old = project_new ; migrateEvents
```

effect boundary は、依存グラフだけでは見えない obstruction を扱う。
許可されない effect、暗黙の authority、handler 欠落、非可換な effect pair は
effect-level obstruction witness として読む。

## 14. Architecture Extension Formula

Architecture Extension Formula は、feature extension の obstruction を分類する構造式である。

```text
ExtensionObstruction
  = inherited core obstruction
  + feature-local obstruction
  + interaction obstruction
  + lifting failure
  + filling failure
  + complexity transfer
  + residual coverage gap
```

これは互いに素な分解を無条件に主張しない。同じ witness が複数の分類を持つことがある。
式の役割は、obstruction の由来を説明可能にすることである。

## 15. Analytic Representation

`AnalyticRepresentation` は、structural architecture object を解析的な値へ写す。

```text
rho : Architecture -> AnalyticDomain
```

representation の強さは少なくとも四つに分かれる。

```text
ZeroPreserving:
  structural zero -> analytic zero

ZeroReflecting:
  analytic zero + assumptions -> structural zero

ObstructionPreserving:
  structural obstruction -> analytic obstruction

ObstructionReflecting:
  analytic obstruction + assumptions -> structural obstruction
```

反映方向には coverage、witness completeness、semantic contract coverage が必要になる。
analytic value だけから structural flatness を読むことはできない。

## 16. 設計原則

AAT では、設計原則を万能の規範として扱わない。
設計原則は、特定の invariant を保存、反映、改善、局所化、翻訳、転送する
operation family として読む。

| 設計原則群 | AAT での読み |
| --- | --- |
| SOLID | 局所契約層の invariant を保存する operation family。 |
| Layered / Clean Architecture | 大域構造層の依存方向、境界、抽象化を保存する operation family。 |
| Event Sourcing / Saga / CRUD | 状態遷移代数層の replay、projection、compensation、永続化境界に関する operation family。 |
| Circuit Breaker / Replicated Log | 実行時依存、保護、収束、分散境界に関する operation family。 |

SOLID は万能原理ではない。局所契約、大域構造、状態遷移、実行時依存、分散収束を
一枚の原理へ潰さず、異なる invariant family として扱う。

## 17. AAT の境界

AAT は証明可能な局所代数を守る。
予測、組織、AI、PRD、Issue、PR、運用、終焉の力学は
[SFT](../sft/README.md) へ分離する。

```text
AAT formalizes the local algebra of software change.
SFT studies the global field dynamics of software evolution.
```
