# ArchSig Private Python Repository AAT Structural Readings Note

とある Python リポジトリの ArchMap を用いた AAT structural readings 実験メモ

---

## 0. Status

この文書は、対象リポジトリの `ArchMap` を入力として ArchSig がどこまで
AAT 的な分析を返せるかを確認した研究メモである。

ここで重要なのは、ArchSig が対象リポジトリの Python source を直接読んだのではなく、
すでに生成された `ArchMap` を読んだ点である。

```text
Private Python repository source
  observed as
ArchMap
  analyzed by
ArchSig
  interpreted by
LLM / human reviewer
```

したがって、このメモの主張は「対象リポジトリの source code を完全に理解した」という
主張ではない。主張しているのは、Atom / Molecule / Law / Obstruction を持つ
ArchMap があれば、通常の静的解析とは異なるアーキテクチャ状態の読みが
可能になる、ということである。

---

## 1. Main Finding

今回の実験で最も大きかった発見は次である。

```text
ArchSig can read architecture state, not only architecture violations.
```

従来の静的解析は、主に source code 上の構文的・依存関係的な事実を読む。
それに対して、ArchSig は `ArchMap + LawPolicy` から、次のような構造状態を読めた。

- どの Molecule が分割準備できていないか
- どの境界が policy / transaction boundary / anti-corruption layer を必要としているか
- どの Law に対して local curvature が出ているか
- static / runtime / semantic の flatness がどこで分離しているか
- state atom と effect atom の代数的関係がどこで未解決か
- repair operation がどの invariant を保てずに止まっているか
- LLM 観測の揺らぎがどの projection loss として現れているか

これは単なる rule violation checker ではない。
違反の有無ではなく、architecture の構造的圧力、曲率、分割準備度、観測境界を
多軸で読む分析である。

---

## 2. Experiment Summary

入力は対象リポジトリの ArchMap である。

```text
<private-archmap-root>/archmap.json
```

ArchSig analysis packet validation は pass した。
追加した AAT structural readings は次の件数で出力された。

```text
representationStrengthReadings      14
localCurvatureDiagramReadings        5
threeLayerFlatnessReadings           1
observationProjectionReadings        1
stateTransitionAlgebraReadings       1
operationInvariantGaloisReadings     1
splitReadinessReadings              13
```

この件数そのものより重要なのは、これらが個別の lint 結果ではなく、
同じ ArchMap 上の AAT reading surface として接続されている点である。

### 2.1 Validation Record

このセッションでは、対象リポジトリの analysis packet 生成だけでなく、
tooling と repository の検証も実施した。

対象リポジトリ analysis は次の形で実行した。

```text
archsig-analysis
  --archmap <private-archmap-root>/archmap.json
  --law-policy <private-archmap-root>/profiles/interpretation_profile.json
  --out <private-archmap-root>/masked-python-repo-profile/archsig-analysis-packet.json
  --validation-out <private-archmap-root>/masked-python-repo-profile/archsig-analysis-validation.json
```

validation summary は pass であり、失敗 check と warning check は 0 だった。

```text
result            = pass
failedCheckCount  = 0
warningCheckCount = 0
```

加えて、ArchSig の実装変更として次を通した。

```text
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
lake build
git diff --check
hidden / bidirectional Unicode scan
Lean forbidden token scan
Rust placeholder / panic-family scan
GitHub Actions CI
```

この検証記録の意味は、対象リポジトリ reading の内容が「正しい真理」と証明されたということではない。
意味しているのは、ArchSig の schema / builder / fixtures / validation / FieldSig handoff /
Lean repository state が同じ boundary のもとで壊れていない、ということである。

```text
validated:
  artifact shape
  schema compatibility
  packet validation
  対象リポジトリ packet generation
  CI reproducibility

not validated:
  complete source extraction
  global architecture truth
  repair correctness
  runtime behavior
```

---

## 3. A Layered Repository, But Not Flat

対象リポジトリは layered architecture を採用している。
しかし、今回の reading では次が出た。

```text
staticStatus   = needsReview
runtimeStatus  = blockedByCoverageGap
semanticStatus = stressed
crossLayerAtoms = 24
```

これは非常に重要である。

Layered architecture は、source layout や module grouping としては成立していても、
AAT 的な flatness を自動的には意味しない。

```text
Static separation
  does not imply
Runtime flatness
  does not imply
Semantic flatness
```

対象リポジトリでは、layer が分かれているように見えても、
contract / state / effect / authority / trust / semantic の atom が
cross-layer に現れている。

このため、局所的な修正が別の場所へ波及する可能性がある。
ユーザーが経験していた「局所修正で思わぬところが壊れた」という現象は、
この reading と整合的である。

---

## 4. Split Readiness Ranking

最も実務的だった reading は `splitReadinessReadings` である。

低 score の Molecule は、今すぐ分割・修正すると複雑性転送が大きい可能性が高い。
対象リポジトリでは上位に次が出た。

```text
molecule:transaction-boundary-alpha
  status   = needsBoundaryPreparation
  score    = 30
  bridges  = 2
  boundary = policy

molecule:domain-artifact-cohesion-beta
  status   = needsBoundaryPreparation
  score    = 30
  bridges  = 2
  boundary = transactionBoundary

molecule:request-authority-boundary-gamma
  status   = needsBoundaryPreparation
  score    = 45
  bridges  = 1
  boundary = policy

molecule:ai-generation-job-surface-delta
  status   = needsBoundaryPreparation
  score    = 53
  bridges  = 1
  boundary = antiCorruptionLayer
```

これは、「どの workflow が危ないか」という問いをより精密にしたものである。

危ないとは、単に bug があるという意味ではない。
次の条件を満たす Molecule は、変更時に複雑性転送を起こしやすい。

- obstruction に参加している
- bridge edge を持つ
- domain artifact / transaction / request authority / AI surface を横断している
- 推奨 boundary operation が interface だけでは足りない

対象リポジトリでは、transaction boundary alpha と domain artifact cohesion beta が
最も強い boundary preparation target として出た。

---

## 5. Transfer Bridge Reading

以前の analysis で特に強かった bridge は次である。

```text
request-authority-boundary-gamma
  -> transaction-boundary-alpha
  -> domain-artifact-cohesion-beta
  -> ai-generation-job-surface-delta
```

今回の split readiness は、この bridge reading を現在状態の分割判断に接続した。

```text
request authority boundary
  carries policy pressure

transaction boundary alpha
  carries policy and transaction pressure

domain artifact cohesion beta
  carries transaction boundary pressure

AI generation job surface delta
  carries anti-corruption pressure
```

ここで見えているのは、対象リポジトリにおいて request authority / transaction / domain artifact / AI generation が
完全に独立したレイヤーとして振る舞っていないということである。

見かけ上のレイヤー分離があっても、Atom の関係としては、
境界をまたいで意味・状態・権限・副作用が接続している。

---

## 6. Spectral Readings

今回の対象リポジトリ analysis では、spectral readings も重要な signal を返した。

ここでの spectrum は、厳密な数値線形代数としての固有値分解そのものではない。
ArchMap 上の Molecule / Atom / Obstruction / Operation を行列的な表現へ写し、
どの成分が支配的な圧力を持つかを読むための AAT structural proxy である。

出力された spectral analysis は次である。

```text
spectral:workflow-risk-axis-pressure
spectral:molecule-atom-overlap-coupling
spectral:obstruction-axis-curvature
spectral:operation-signature-delta
```

### 6.1 Workflow risk axis pressure

`workflowRiskAxisPressureMatrix` では、支配的な workflow と axis が読めた。

```text
dominant workflow:
  molecule:ai-generation-job-surface-delta
  value = 110

dominant axis:
  domainArtifactCohesion
  value = 235
```

これは、対象リポジトリにおける AI generation surface が
workflow risk の強い行として現れ、同時に domain artifact cohesion が
全 workflow 横断の支配的な列として現れていることを意味する。

つまり、LLM 周辺だけが危ないのではない。
AI generation surface が、domain artifact cohesion の圧力を強く受ける位置にある。

これは以前の bridge reading と整合する。

```text
domain-artifact-cohesion-beta
  -> ai-generation-job-surface-delta
```

### 6.2 Molecule atom overlap coupling

`moleculeAtomOverlapCouplingMatrix` では、支配的な molecule として
次が出た。

```text
dominant molecule:
  molecule:request-authority-boundary-gamma
  value = 42
```

これは request authority boundary gamma が、atom / atom family overlap の観点で
大きな結合質量を持つことを示す。

対象リポジトリでは request authority boundary が単なる edge adapter ではなく、
authority、contract、relation をまとめて担う semantic hub として現れている。

このため、request authority boundary を局所修正すると、
auth lifecycle、transaction boundary、observability、permission coverage へ
影響が転送されやすい。

### 6.3 Obstruction axis curvature

`obstructionAxisCurvatureMatrix` では、支配的な obstruction / axis として
state-effect reconciliation が出た。

```text
dominant obstruction:
  obstruction:private-python-repo-state-effect-reconciliation-gap:computed

dominant axis:
  sig-axis:private-python-repo-state-effect-reconciliation-gap
```

これは、対象リポジトリの curvature が単に依存方向の問題ではなく、
state と effect の整合問題として強く現れていることを示す。

この reading は state transition algebra reading と接続する。

```text
state atoms
effect atoms
runtime atoms
  generate
state transition algebra pressure

unresolved relation:
  state-effect reconciliation
```

### 6.4 Operation signature delta

`operationSignatureDeltaMatrix` では、支配的な operation delta として
state-effect reconciliation repair が出た。

```text
dominant operation delta:
  operation-delta:repair-obstruction-private-python-repo-state-effect-reconciliation-gap-computed
  value = 5

dominant touched axis:
  sig-axis:private-python-repo-state-effect-reconciliation-gap
```

ただし、各 repair operation は target-positive axis を 1 つ持つ一方で、
他の 4 axis を negative / transferred axis として持っていた。

```text
positiveDeltaAxes = 1
negativeDeltaAxes = 4
```

これは非常に重要である。

対象リポジトリでは、ある obstruction を直す operation が、他の obstruction axis へ
複雑性を転送する可能性を持つ。

```text
repair one axis
  may transfer pressure to
authority / trust
permission coverage
domain artifact cohesion
AI output mediation
state-effect reconciliation
```

このため、対象リポジトリの repair は単独 axis の改善として見るべきではない。
operation signature delta を見て、どの axis が正に改善され、
どの axis に副作用が出るかを読んでから実行すべきである。

### 6.5 Dominant atom family composition

Spectral drilldown は、dominant mode の atom family composition も返した。

特に重要だった構成は次である。

```text
molecule:ai-generation-job-surface-delta
  capability = 3
  state      = 3
  effect     = 2
  trust      = 1

molecule:request-authority-boundary-gamma
  authority             = 3
  contractSpecification = 3
  relation              = 1
```

これは対象リポジトリの dominant pressure が、
AI surface 側では capability / state / effect / trust として、
request authority boundary 側では authority / contract / relation として現れていることを示す。

この構成は設計レビューで有用である。

```text
AI generation side:
  capability, state, effect, trust

request authority side:
  authority, contract, relation
```

したがって、対象リポジトリの大きな構造圧力は、
AI 実行面と request authority 面の 2 つの dominant mode として読める。

### 6.6 High-overlap molecule pairs

Spectral drilldown は high-overlap molecule pair も返した。
上位は次である。

```text
provider-integration-ingress
  <-> external-provider-event-processing
  overlapScore = 12
  sharedAtomFamilies = contractSpecification, effect, trust

request-authority-boundary-gamma
  <-> edge-observability-policy
  overlapScore = 11
  sharedAtomFamilies = authority, contractSpecification

request-authority-boundary-gamma
  <-> auth-session-lifecycle
  overlapScore = 9
  sharedAtomFamilies = contractSpecification

privileged-user-auth-lifecycle
  <-> privileged-governance-action
  overlapScore = 9
  sharedAtomFamilies = authority, capability, contractSpecification

transaction-boundary-alpha
  <-> domain-artifact-cohesion-beta
  overlapScore = 8
  sharedAtomFamilies = capability, contractSpecification, state
```

これは「凝集度と結合度」を ArchSig 的に読むうえで強い。

通常の coupling は import / call / dependency の数で読まれがちである。
しかし ArchSig では、Molecule 間で共有されている Atom family を読む。

```text
static coupling:
  module A imports module B

ArchSig overlap coupling:
  molecule A and molecule B share authority / state / effect / trust / contract atoms
```

この差により、source-level edge が少なくても、
semantic overlap が大きいペアを見つけられる。

対象リポジトリの場合、request authority 周辺と external provider 周辺に、
意味論的な overlap hub がある。

### 6.7 Spectral conclusion

対象リポジトリの spectrum は、次を示している。

```text
dominant workflow pressure:
  ai-generation-job-surface-delta

dominant semantic pressure axis:
  domain-artifact-cohesion

dominant molecule overlap hub:
  request-authority-boundary-gamma

dominant curvature axis:
  state-effect-reconciliation

dominant repair transfer risk:
  every single-axis repair touches four other axes
```

これは、対象リポジトリの安全な改善順序を考える上で大きい。

まず単一 repair を当てるのではなく、request authority boundary、transaction boundary、
domain artifact、AI surface の shared atom families を読み、
operation delta がどの axis へ複雑性を転送するかを確認する必要がある。

---

## 7. Local Curvature

`localCurvatureDiagramReadings` は 5 つ出た。

```text
law:private-python-repo-authority-trust-boundary
law:private-python-repo-state-effect-reconciliation
law:private-python-repo-domain-artifact-cohesion
law:private-python-repo-ai-output-mediation
law:private-python-repo-permission-coverage
```

ここでの curvature は、「依存方向が悪い」という単純な意味ではない。

AAT 的には、Law が期待する diagram filling が、観測された Molecule / Atom 配置では
局所的に埋まらない状態として読む。

```text
expected diagram
  should commute / fill under the selected Law

observed architecture
  leaves a nonzero local obstruction

reading
  local curvature
```

この表現が有用なのは、設計の悪さを単一カテゴリに潰さない点である。

authority / trust の曲率と、state / effect の曲率と、AI output mediation の曲率は
同じ「違反」ではない。それぞれ異なる Law に対する異なる局所歪みである。

---

## 8. State Transition Algebra

対象リポジトリでは state transition algebra reading がかなり強い signal を返した。

```text
generatorRefs = 48
stateAtoms    = 40
effectAtoms   = 40
runtimeAtoms  = 10

obstruction:
  obstruction:private-python-repo-state-effect-reconciliation-gap:computed
```

ArchSig は次の未解決関係を残した。

```text
runtime-and-provider-traces
route-by-route-permission-audit
model-relationship-completeness
test-evidence-not-read
```

また、次に見るべき観点として次を出した。

```text
idempotency
replay
ordering
transaction ownership
```

これは実務上かなり重要である。

状態と副作用が強く絡む system では、局所修正の安全性は
単体 test や型だけでは読みにくい。

AAT 的には、state atom と effect atom が生成する遷移代数に対して、
順序、再実行、transaction ownership、外部 effect の境界が整理されているかを見る。

対象リポジトリの reading は、この点で「まだ代数的に閉じていない領域」を示している。

---

## 9. Representation Strength And Non Conclusion

今回の representation strength reading では、多くの representation について
次が出た。

```text
zeroReflecting        = blockedByCoverageGap
obstructionReflecting = blockedByCoverageGap
blockedBy             = 5
```

これは弱点ではなく、実務投入に必要な境界である。

ArchSig の出力は LLM 観測に依存する。
したがって、ArchSig は「これは確定した真実である」とは言わない。

しかし、non conclusion で止まるのでもない。

今回の設計では、non conclusion を次の形に変換する。

```text
unknown truth
  not as
analysis failure

unknown truth
  as
projection loss / coverage gap / representation strength boundary
```

これは、経済学に近い距離感である。

経済学者は経済そのものを直接見ることはできない。
統計、価格、行動、制度、事件を通じて間接的に読む。
それでも経済学は non conclusion ではない。

ArchSig も同様に、architecture の完全な真実を直接見るのではなく、
Atom observation の projection から構造状態を読む。
その際、何を忘れているか、どの representation が何を保存し、何を反映しないかを
明示する。

---

## 10. Observation Projection

対象リポジトリの observation projection reading は次を示した。

```text
observedAtomFamilies = 8

forgottenCoordinates:
  gap:per-file-semantic-coverage
  gap:runtime-and-provider-traces
  gap:route-by-route-permission-audit
  gap:model-relationship-completeness
  gap:test-evidence-not-read
```

この reading の意味は大きい。

LLM が生成した ArchMap は、source architecture の完全な同型コピーではない。
それは canonical Atom family への projection である。

```text
Architecture
  has canonical Atom family

ArchMap
  observes a projection of that family

ArchSig
  analyzes the projection
  while recording lost coordinates
```

この整理により、LLM 観測の揺らぎは「信頼できないから使えない」ではなく、
「どの coordinate を忘れた projection か」として扱える。

---

## 11. Operation-Invariant Galois Reading

対象リポジトリでは operation-invariant Galois reading が次を返した。

```text
invariants = 5
operations = 5
blockedOperations = 5
```

blocked operation は次の obstruction repair に対応している。

```text
private-python-repo-authority-trust-boundary-stress
private-python-repo-state-effect-reconciliation-gap
private-python-repo-domain-artifact-cohesion-stress
private-python-repo-ai-output-mediation-stress
private-python-repo-permission-coverage-gap
```

この reading の狙いは、repair operation を単なる修正候補として出すことではない。

```text
Operation
  should preserve / improve
Invariant family

Invariant family
  constrains admissible operations
```

この往復を Galois-style reading として扱う。

つまり、ある repair が可能かどうかは、その repair がどの invariant を壊さずに
実行できるかに依存する。

これは、AI が高速に code を生成する時代に特に重要である。
AI は局所的な patch を速く作れるが、その patch が architecture invariant を
保存しているかは別問題である。

ArchSig は、この別問題を review surface として出す。

---

## 12. Why This Is Not Just Static Analysis

今回の実験で、ArchSig は対象リポジトリの source code を直接読まずに、
次のような判断を返した。

- layered architecture が flatness を意味しない
- request authority / transaction / domain artifact / AI surface の間に bridge pressure がある
- transaction boundary alpha と domain artifact cohesion beta は先に境界整理すべき
- state/effect reconciliation は transition algebra の問題として見える
- AI output mediation は anti-corruption layer を必要とする
- authority/trust と permission coverage は別の曲率として出る
- non conclusion は coverage gap と representation boundary に変換できる

これは通常の静的解析では簡単ではない。

静的解析は source-level edge を読める。
しかし、source-level edge がどの Atom family に属し、どの Molecule を構成し、
どの Law に対して obstruction になり、どの repair operation がどの invariant を
保てるかまでは、通常は読まない。

ArchSig の強みはここにある。

```text
Static analysis:
  source edge / import / call / type / dependency

ArchSig:
  Atom / Molecule / Law / Obstruction / Invariant / Operation
```

この差分により、ArchSig は「違反チェッカー」ではなく、
architecture review のための structural telemetry になる。

---

## 13. Review Workflow Implication

実務上の最も大きな使い方は review である。

AI が高速に code を生成する環境では、単体 test や CI は局所的な破損を検知できる。
しかし、architecture の構造的悪化は見落としやすい。

ArchSig は、review 前に次を出せる。

```text
before reviewing a patch:
  read related Atom families
  read touched Molecules
  read bridge edges
  read split readiness
  read local curvature
  read operation-invariant constraints
```

これにより、reviewer は単に diff を読むのではなく、
diff が触る architecture state を読むことができる。

この観点では、ArchSig は PR reviewer を置き換えない。
PR reviewer が見るべき構造面を先に照らす。

PR/diff/change-vector そのものは FieldSig 側の領域である。
ArchSig は現在の architecture state を読む。
FieldSig は、その state が変更によってどう動くかを読む。

### 13.1 Private Python Repository Review Queue

このセッションで得た対象リポジトリ向けの review queue は次のように整理できる。

```text
1. transaction-boundary-alpha
   first concern:
     transaction ownership and policy boundary

2. domain-artifact-cohesion-beta
   first concern:
     domain artifact cohesion and transaction boundary

3. request-authority-boundary-gamma
   first concern:
     authority / contract / relation hub

4. ai-generation-job-surface-delta
   first concern:
     anti-corruption layer for AI effects and trust boundary

5. state-effect-reconciliation
   first concern:
     idempotency, replay, ordering, transaction ownership
```

この順序は、単なる危険度 ranking ではない。

`splitReadiness`, `transferBridge`, `spectralDrilldown`,
`stateTransitionAlgebra`, `operationSignatureDelta` を重ねたとき、
先に境界整理すべき architecture state がこの順に見えた、という reading である。

実際の review では、各対象について次を読む。

```text
target molecule
  -> shared atom families
  -> bridge edges
  -> local curvature refs
  -> positive / negative repair delta axes
  -> missing observation coordinates
```

この queue は、AI-generated patch の review にそのまま使える。
patch がどの source file を触ったかだけでなく、
どの Molecule / Atom family / Law axis を揺らすかを読むための入口になる。

---

## 14. Research Direction

今回の実験から、次の方向が強い。

### 14.1 Source refs down to bridge edges

Transfer Bridge 上の各 edge を source refs まで落とす。

```text
request-authority-boundary-gamma
  -> transaction-boundary-alpha

transaction-boundary-alpha
  -> domain-artifact-cohesion-beta

domain-artifact-cohesion-beta
  -> ai-generation-job-surface-delta
```

各 edge について次を読む。

- 共有 atom family は何か
- source refs は何か
- 明示 contract か、暗黙依存か
- interface / policy / transaction boundary / anti-corruption layer のどれで切るべきか

### 14.2 FieldSig handoff

ArchSig は current architecture state を読む。
FieldSig は PR / diff / change vector による evolution を読む。

したがって、次の boundary が重要になる。

```text
ArchSig:
  current AAT structural state

FieldSig:
  software evolution over ArchSig state
```

### 14.3 AAT mathematical expansion

今回の readings は、AAT 数学本文の概念を tooling surface に落とす最初の成功例である。

特に次は強い。

- representation strength
- spectral proxy / spectral drilldown
- local curvature
- three-layer flatness
- observation projection
- state transition algebra
- operation-invariant Galois connection
- split readiness

これらはすべて、単一スコアではなく、多軸 structural reading として扱うべきである。

---

## 15. Conclusion

今回の対象リポジトリ実験は、ArchSig の方向性が正しいことを強く示している。

```text
Atom is all you need
```

Atom があることで、source code をただの文字列や dependency graph としてではなく、
architecture の typed fact family として読める。

Molecule があることで、局所的な設計単位を読める。
Law があることで、設計原則を rule ではなく構造的期待として読める。
Obstruction があることで、違反を単なる error ではなく local curvature として読める。
Repair operation があることで、修正を invariant-preserving operation として読める。

ArchSig の役割は、AAT のための解析機である。

```text
ArchMap observes Atoms.
ArchSig applies AAT.
FieldSig studies evolution.
LLM reads the packet and lowers cognitive load.
```

対象リポジトリの結果は、ArchSig が開発現場の pain に届き始めていることを示している。

AI が高速に code を生成する時代には、局所 test と CI だけでは足りない。
必要なのは、architecture state を読むための structural telemetry である。

ArchSig は、その telemetry になりうる。
