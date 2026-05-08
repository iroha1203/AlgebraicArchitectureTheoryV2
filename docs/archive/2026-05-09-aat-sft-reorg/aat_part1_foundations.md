# Part 1: AAT 基礎編

## 1. 中心命題

AAT は、ソフトウェア開発を単なるコード変更の列としてではなく、architecture の
拡大、分解、修復、合成の理論として扱う。

第一対象は incident ではなく **feature addition** である。incident は、悪い拡大により
導入された obstruction が実行時や運用時に表面化した manifestation として読む。

中心命題は次である。

```text
software development
  = architecture extension
  + operation
  + invariant
  + obstruction witness
  + proof obligation
  + certificate
```

この見方では、設計レビューの主な問いは「よいか悪いか」ではなく、次の形になる。

```text
- 既存構造は拡大後にも埋め込まれているか。
- 新機能は既存構造から split して取り出せるか。
- 相互作用は宣言された interface を通るか。
- どの invariant が保存され、どの invariant が破れたか。
- split しないなら、どの obstruction witness が妨げているか。
```

## 2. ArchitectureCore

`ArchitectureCore` は、AAT が扱う最小の architecture object である。

```text
ArchitectureCore :=
  components
  + static dependency relation
  + runtime dependency relation
  + boundary policy
  + abstraction policy
  + observation model
  + semantic diagram universe
```

`components` は測定または議論の universe を与える。依存関係は static と runtime に
分かれ、boundary policy は許可される依存と禁じられる依存を区別する。
abstraction policy は projection、refinement、quotient を扱い、observation model は
実装上の同一性ではなく観測上の同値性を読むための窓を与える。

`ArchitectureCore` は、実コードベースそのものではない。実コード、仕様、レビュー、
運用観測から切り出された、理論が扱える有限または bounded な対象である。

### ComponentUniverse

`ComponentUniverse` は、測定または議論の対象を保持する proof-carrying universe である。
ここで重要なのは、universe が「全コードベースの完全抽出」を意味しないことである。

```text
ComponentUniverse :=
  selected components
  + selected relations
  + evidence boundary
  + coverage boundary
  + exactness boundary
```

この universe の外側にある component や relation について、AAT は zero を主張しない。
zero、absence、flatness、split は、常に選ばれた universe と observation に相対化される。

### ComponentCategory

`ComponentCategory` は、component 間の到達可能性を扱う thin category として読む。
thin category では、二つの component の間に射が存在するかだけを保持し、path count や
walk length は忘れる。

```text
reachable A B
  = there exists a dependency path from A to B
```

したがって、到達可能性の有無を扱う theorem と、path 数、walk 長、伝播量、重み付き影響を
扱う analytic reading は分ける。後者は `Walk`、`Path`、adjacency matrix、または別の
free-category 的表現に載せる。

### Decomposable

`Decomposable` は、選ばれた層構造に対する `StrictLayered` として読む。
acyclicity、finite propagation、nilpotence、spectral condition は、`Decomposable` の定義に
混ぜない。それらは、別の theorem、別の representation、または別の proof obligation として
接続する。

## 3. FeatureExtension

機能追加は、既存 architecture を保ったまま、より大きな architecture へ拡大する操作である。

```text
ExistingCore X
  -> ExtendedArchitecture X'
  -> FeatureView F
```

`FeatureExtension X F X'` は、少なくとも次を持つ。

```text
coreEmbedding : X -> X'
featureView   : X' -> F
interaction   : F x X -> relation
```

ここで重要なのは、新機能 `F` が単独で存在するのではなく、既存構造 `X` に対する
拡大として現れることである。良い機能追加は、既存構造を壊さず、新機能差分を
説明可能な形で取り出せる。

## 4. Split Extension

`SplitFeatureExtension` は、拡大後の architecture が既存 core と feature view に
分解できることを表す数学的な full split package である。

```text
SplitFeatureExtension X F X' :=
  embeddingPreserved
  + featureViewSection
  + declaredInterfaceFactorization
  + selectedInvariantPreservation
  + noHiddenInteraction
```

直感的には、次の条件を要求する。

```text
- 既存 core は拡大後にも保存される。
- feature view は取り出せる。
- feature から core への相互作用は宣言された interface を通る。
- 選択された invariant は保存される。
- hidden dependency や policy bypass が混入しない。
```

ただし AAT では、この full split package を一つの入口に圧縮しない。
理論上の構成要素として、少なくとも次を分けて扱う。

```text
FeatureExtension
  = core embedding と feature view を持つ拡大そのもの

StaticSplitFeatureExtension
  = static relation と boundary policy に関する split evidence

SplitExtensionLiftingData
  = feature step が declared interface を通って持ち上がるための lifting evidence

SplitFeatureExtensionWithin
  = universe、observation、invariant family に相対化された split claim
```

この分解により、static split、runtime evidence、semantic evidence、lifting evidence を混同しない。
たとえば static split が成り立っても、runtime protection や semantic diagram filling は別の
前提を必要とする。

split は全宇宙の完全分解ではない。AAT では、どの universe、どの observation、
どの invariant family に相対化して split を読むかを明示する。

## 5. Invariant

`Invariant` は、architecture object や operation が保存すべき性質である。

例として次がある。

```text
- dependency direction
- boundary policy
- abstraction policy
- observation equivalence
- local contract
- replay law
- compensation law
- runtime protection
- convergence condition
```

設計原則は、invariant を直接置き換えるものではない。設計原則は、どの invariant を
選び、どの operation family がそれを保存するかを指定する語彙である。

## 6. Obstruction Witness

`ObstructionWitness` は、ある望ましい性質が成り立たない理由を構造的に示す対象である。

代表例は次である。

```text
- forbidden static edge
- hidden interaction
- boundary policy violation
- abstraction leakage
- non-commuting semantic diagram
- runtime exposure
- lifting failure
- filling failure
- complexity transfer
- residual coverage gap
```

obstruction は単なるエラーではない。修復、分類、不能性証明、または進化軌道の変化を
説明するための witness である。

## 7. Law Universe と Zero

`LawUniverse` は、architecture に要求する法則族を束ねる。

```text
LawUniverse :=
  required laws
  + optional laws
  + derived laws
  + witness family
  + observation boundary
```

lawfulness は、obstruction absence と同じものとして最初から定義しない。
まず意味論的な lawfulness を置き、次に finite witness family を通じて obstruction absence と
接続する。

```text
Lawful X L
NoRequiredObstruction X L
RequiredAxesAvailableAndZero L sig
```

AAT の基本形は、これらを同じ現象の別表現として読むことである。

```text
lawfulness
  <-> no required obstruction witness
  <-> required signature axes are available and zero
```

この読みは、universe、coverage、exactness、observation boundary に相対化される。
未観測軸や対象外の law を zero と読まない。

## 8. Zero-count Kernel

obstruction family を有限に測る最小核は、bad witness の列と count である。

```text
violatingWitnesses bad xs :=
  xs filtered by bad

violationCount bad xs :=
  length (violatingWitnesses bad xs)
```

有限 witness universe では、zero-count は selected witness absence と対応する。

```text
violationCount bad xs = 0
  <-> every measured witness is not bad
```

この核は小さいが重要である。dependency cycle、projection failure、observation mismatch、
semantic diagram failure、effect leakage などは、それぞれ異なる witness family として
この核へ載せられる。

## 9. Architecture Curvature

AAT では、architecture quality の破れを、要求された法則族に対する非零 obstruction として
読む。可換であるべき図式が可換でないことは、その代表例である。

```text
required relation:
  lhs ~ rhs

semantic observation:
  Obs(lhs) != Obs(rhs)

curvature:
  nonzero obstruction witness
```

依存循環、抽象化の射影失敗、置換不能性、replay failure、roundtrip loss、effect leakage は、
互いに異なる domain の現象である。しかし AAT では、それらを「要求法則族に対する
obstruction witness」として統一的に読む。

## 10. Proof Obligation

`ProofObligation` は、operation や theorem package が要求する前提と結論を明示する schema
である。

```text
ProofObligation :=
  formalUniverse
  + requiredLaws
  + invariantFamily
  + witnessUniverse
  + coverageAssumptions
  + exactnessAssumptions
  + operationPreconditions
  + conclusion
  + nonConclusions
```

`nonConclusions` は必須である。ある static split が与えられても、runtime flatness や
semantic flatness は自動的には従わない。ある observation universe で obstruction が
見つからなくても、全 universe で obstruction が存在しないとは限らない。

## 11. Certificate と Claim Boundary

`CertifiedArchitecture` は、architecture object に claim と certificate boundary を添えた
対象である。

```text
CertifiedArchitecture :=
  architecture
  + claims
  + evidence boundary
  + measurement boundary
  + nonConclusions
```

`ArchitectureClaim` は、何を、どの水準で、どの observation boundary に相対化して主張するかを
分ける。

```text
ArchitectureClaim :=
  subject
  + predicate
  + claim level
  + measurement boundary
  + assumptions
  + nonConclusions
```

claim level は、形式的主張、観測に基づく主張、実証的主張、仮説的主張を区別する。
measurement boundary は、selected universe で zero が見えた場合、nonzero witness が
見えた場合、未観測の場合、対象外の場合を区別する。

この節は作業状態を管理するためのものではない。AAT の certificate は、数学的主張が
どの universe、どの evidence、どの observation、どの non-conclusion に依存するかを
明示するための境界である。

## 12. Architecture Signature

`ArchitectureSignature` は、architecture quality を単一スコアに潰すためのものではない。
複数の invariant や obstruction family を、軸ごとに読むための多軸診断である。

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

各軸は、測定可能性、coverage、exactness、observation model に相対化される。
未観測の軸を zero と読んではならない。zero は、選ばれた universe と前提のもとでのみ
意味を持つ。

より強く言えば、`ArchitectureSignature` は obstruction witness family の座標表示である。

```text
ArchitectureSignature(X)
  = coordinates of selected obstruction families of X
```

この見方では、signature は便利な metric 集ではなく、law universe に相対化された
多軸不変量である。別の risk measure が law-preserving operation に対して単調であり、
unmeasured と zero を区別し、counterexample witness を非零へ写すなら、その measure は
signature を通じて読める、という普遍性が期待される。

```text
Architecture
  -> ArchitectureSignature
  -> other risk vector
```

## 13. Three-layer Flatness

AAT の flatness は、少なくとも三層に分かれる。

```text
static flatness
runtime flatness
semantic flatness
```

static flatness は依存方向、境界、抽象化の破れを扱う。runtime flatness は実行時依存、
保護、伝播、露出を扱う。semantic flatness は観測上の可換性、diagram filling、
contract preservation を扱う。

三層は互いに独立である。static flatness だけから runtime flatness や semantic flatness は
従わない。統合 flatness は、各層の universe、coverage、exactness、non-conclusion を
そろえた certificate として読む。

## 14. Canonical Example: Coupon Feature Extension

coupon feature extension は、AAT の最小例として使える。

```text
X  = existing order / payment core
F  = coupon discount feature
X' = core extended with coupon behavior
```

良い extension では、coupon の計算は declared interface を通り、payment core への相互作用は
明示された boundary に収まる。悪い extension では、coupon service が payment adapter や
hidden cache に直接依存し、feature-local な都合が core 側の invariant を破る。

この例では、hidden interaction は static obstruction witness として読める。
rounding order や discount application order の観測差は semantic obstruction witness として
読める。同じ題材を、発展編では repair、lifting、diagram filling の例として、力学編では
trajectory と attractor の例として読む。

## 15. 基礎編の境界

基礎編が与えるのは、次の語彙である。

```text
ArchitectureCore
ComponentUniverse
ComponentCategory
Decomposable
FeatureExtension
SplitFeatureExtension
Invariant
ObstructionWitness
LawUniverse
Zero-count Kernel
ProofObligation
CertifiedArchitecture
ArchitectureClaim
ArchitectureSignature
Flatness
```

この語彙により、AAT は「設計が良いか悪いか」という評価を、どの extension がどの
invariant を保存し、どの obstruction がどの split を妨げるかという診断へ変換する。
