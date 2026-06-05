# ArchSig v0.3.0 Measurement Expansion PRD

この PRD は、ArchSig v0.3.0 で追加する計測面の要求を定義する。

v0.3.0 の主目的は、ArchSig の tool quality、review UX、release packaging、
authoring workflow を磨くことではない。v0.3.0 は、AAT 数学本文から
ArchSig analysis packet へ落とせる measurement coordinate を増やす release とする。

中心方針は次である。

```text
ArchMap
  -> ArchSig
  -> more measurable AAT structural coordinates
  -> later review / workflow / product quality releases
```

ArchSig v0.3.0 は、architecture state を単一 score や合否判定に潰さず、
Atom、observation、law universe、feature extension、operation path、diagram、
aggregate boundary に関する計測軸を増やす。

## 要求

### R0. v0.3.0 を Measurement Expansion Release として定義する

v0.3.0 は、既存の `archsig-analysis-packet-v0` の方向性を引き継ぎ、
AAT 的に計測できる architecture coordinate を増やすことを優先する。

優先順位は次である。

```text
new measurable AAT coordinates
  > claim boundary clarity
  > schema / fixture reproducibility
  > review workflow polish
  > packaging / release UX
```

tool quality、summary UX、large-repository authoring ergonomics、release bundle の完成度、
CI / PR review 向けの使いやすさは、v0.7.0 以降の主題として扱う。

v0.3.0 では、計測軸が荒削りであっても、次を満たすなら採用できる。

- ArchMap observation、LawPolicy、または ArchSig analysis packet 内の既存 reading から
  bounded に算出できる。
- AAT 数学本文の概念に対応している。
- source refs、observation refs、coverage boundary、non-conclusions を保持できる。
- theorem proof、global architecture truth を主張しない。

### R1. Atom support / axis restriction を計測する

ArchSig は、Atom family の support と axis restriction を current architecture state の
計測面として出力できなければならない。

AAT 本文では、Atom family `F` に対して次が定義される。

```text
support(F) = { subject(a) | a in F }
F|x = { a in F | axis(a) = x }
```

v0.3.0 では、molecule、workflow、subsystem、selected source universe について、
少なくとも次を計測対象にする。

- support size
- subject family spread
- axis restriction counts
- axis concentration
- mixed-axis molecule pressure
- high-support molecule / law / obstruction refs

この reading は、component 数や dependency edge 数の代替ではない。
state、effect、contract、authority、semantic、runtime interaction を含む Atom support の
広がりを読むための multi-axis measurement とする。

### R2. Atom compatibility / conflict を計測する

ArchSig は、Atom family 内の compatibility と conflicting payload を計測できなければならない。

AAT 本文では、Atom family `F` が compatible であるとは、同じ subject と predicate に対して
矛盾する payload を同時に含まないことをいう。

```text
Compatible(F)
  iff not exists a b in F,
      sameSlot(a,b) and inconsistent(payload(a), payload(b))
```

v0.3.0 では、少なくとも次を計測対象にする。

- same-slot conflict count
- conflicting atom observation refs
- conflicting semantic observation refs
- payload inconsistency kind
- payload comparison policy
- compatibility status
- confidence / uncertainty boundary

この reading は、LLM 観測の不一致、docs / code のズレ、同じ概念への異なる semantic reading を
単なる曖昧さとして潰さず、Atom compatibility boundary として扱う。

`payload` は ArchMap の Atom observation では `objectRefs`, `observationStatus`,
`confidence`, `uncertainty`, `sourceRefs`, and referenced semantic observations
として観測される。ArchSig は same subject / predicate slot を pairwise に比較し、
incompatible object refs、contradictory boolean claim、status / confidence
divergence、semantic observation divergence を別 kind として残す。

Compatibility conflict は、global semantic incorrectness の証明ではない。
ArchSig は、conflict を source-grounded review target として出力する。

### R3. Observation non-injectivity / reconstruction loss を計測する

ArchSig は、ArchMap が canonical Atom family の粗い projection であることを前提に、
observation の情報落ちをより細かく計測できなければならない。

AAT 本文では、観測は canonical Atom family から観測値への写像として読む。

```text
obs : F -> O
```

`obs` が単射でない場合、異なる Atom が同じ観測値へ潰れる。
また、観測値に現れない Atom が存在しないとは限らない。

v0.3.0 では、少なくとも次を計測対象にする。

- observation collision pairs
- collapsed atom family candidates
- coarse projection refs
- hidden atom family hints
- reconstruction blockers
- source / observed / forgotten projection coordinates
- typed non-injectivity candidates and reconstruction blocker evidence refs
- reconstruction risk
- forgotten coordinate count

この reading は、既存の observation projection reading を拡張する。
目的は、LLM-native ArchMap を「不完全だから使えない」と扱うことではなく、
どの座標が潰れ、どの canonical Atom へ戻る情報が足りないかを測ることである。

### R4. Law universe coverage / witness exactness を計測する

ArchSig は、selected interpretation profile がどの law universe をどの程度測れているかを
計測できなければならない。

AAT 本文では、LawUniverse は次の成分を持つ。

```text
required laws
optional laws
derived laws
witness family
selected reading
coverage assumptions
exactness assumptions
```

v0.3.0 では、少なくとも次を計測対象にする。

- required law coverage
- optional law coverage
- witness family coverage
- signature axis coverage
- exactness assumption status
- unmeasured required law count
- blocked witness refs
- law / witness / axis alignment

この reading は、LawPolicy の良し悪しを単一 score で評価しない。
同じ ArchMap でも、selected law universe と witness family が違えば測れるものが変わる。
ArchSig は、その可視範囲と exactness boundary を artifact として出力する。

### R5. Feature Extension Formula axes を計測する

ArchSig は、feature extension の obstruction を AAT 本文の Architecture Extension Formula に
沿って分類・計測できなければならない。

AAT 本文では、feature extension の obstruction は次の構造式として読む。

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

v0.3.0 では、PR / diff そのものを解析対象にしなくても、current ArchMap 上の
feature-like molecule、extension-like operation candidate、repair candidate、semantic observation から、
少なくとも次の軸を出力できるようにする。

- inherited core obstruction refs
- feature-local obstruction refs
- interaction obstruction refs
- lifting failure refs
- filling failure refs
- complexity transfer refs
- residual coverage gap refs
- extension obstruction classification summary

これは FieldSig の PR / diff evolution analysis ではない。
ArchSig は current architecture state に含まれる extension pressure と extension obstruction
coordinates を計測する。実際の変更ベクトル上でどう動くかは FieldSig の責務である。

### R6. Operation calculus law axes を計測する

ArchSig は、operation kind だけではなく、operation calculus law の観測状態を計測できなければならない。

AAT 本文では、operation calculus の law は precondition、selected observation、
witness family、exactness assumption に相対化される。

v0.3.0 では、少なくとも次の operation law axes を計測対象にする。

- composition status
- associativity under observation status
- refinement / abstraction compatibility
- replacement equivalence
- protection idempotence
- runtime localization
- migration compatibility
- reverse involution
- repair monotonicity
- synthesis / no-solution boundary

この reading は、operation tag から theorem を導くものではない。
例えば `Protect` という tag があるだけでは protection idempotence は従わない。
ArchSig は、selected observation と evidence refs の範囲で、各 operation law が
observed、unmeasured、blocked、not applicable のどれかを出力する。

### R7. Path signature trajectory を計測する

ArchSig は、operation path を endpoint delta だけでなく signature trajectory として計測できなければならない。

AAT 本文では、architecture path は operation の列であり、path observation は各 step の
signature 変化として読める。

```text
Sig(A_0), Sig(A_1), ..., Sig(A_n)
```

v0.3.0 では、current packet 内の repair operation candidates、operation deltas、
path / homotopy / diagram readings を使い、少なくとも次を計測対象にする。

- endpoint signature delta
- max axis excursion
- non-monotone axis refs
- path cost proxy
- preserved invariant trajectory
- introduced obstruction trajectory
- trajectory coverage boundary

この reading は、実 PR の before / after trajectory を直接測るものではない。
ArchSig は current state から読める candidate path の structural trajectory を測る。
実際の repository evolution trajectory は FieldSig の責務である。

### R8. Homotopy / operation-order sensitivity を計測する

ArchSig は、異なる operation order が selected observation 上で同じ architecture transformation として
読めるかを計測できなければならない。

AAT 本文では、二つの path が homotopic であるとは、選ばれた generator によって
相互に変形できることをいう。

v0.3.0 では、少なくとも次を計測対象にする。

- independent square candidate refs
- same-contract replacement refs
- repair filler refs
- operation order sensitivity
- homotopy blocker refs
- selected observation preservation status

この reading は、同じ endpoint を持つ二つの path が常に同じであるとは主張しない。
むしろ、同じ target に見える変更でも、途中で保存される invariant、導入される obstruction、
signature trajectory が違いうることを計測対象にする。

### R9. Diagram fillability を計測する

ArchSig は、diagram が埋められるか、またはどの missing filler によって blocked されているかを
計測できなければならない。

AAT 本文では、diagram filling は部分的に与えられた architecture diagram を完成できるかを問う。

```text
Fill(D)
not exists fill, Fill(D, fill)
```

v0.3.0 では、local curvature diagram reading を拡張し、少なくとも次を計測対象にする。

- diagram family
- missing filler kind
- filler candidate refs
- non-fillability witness refs
- filling blocker refs
- relation to obstruction refs
- relation to feature extension lifting / filling failure

この reading は、全ての split failure を diagram filling failure へ還元しない。
還元するには、selected diagram family、lifting data、filling condition が必要であり、
ArchSig はその boundary を出力する。

### R10. Representation Strength safety を計測する

ArchSig は、analytic representation、spectral proxy、matrix reading、curvature value、
aggregate が、構造的状態をどの向きに保存・反映するかを計測できなければならない。

AAT 本文では、analytic representation の強さは少なくとも四つに分かれる。

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

v0.3.0 では、少なくとも次を計測対象にする。

- representation family
- source reading refs
- zero-preserving status
- zero-reflecting status
- obstruction-preserving status
- obstruction-reflecting status
- required assumptions
- blocked reflection / preservation reason
- coverage / witness completeness blockers

この reading は、analytic value を architecture object 全体の代替にするためのものではない。
matrix、spectral proxy、curvature、aggregate を使う場合に、何を保存でき、何を戻せず、
どの assumption が足りないかを明示するための boundary measurement である。

Aggregate zero の安全性は、この representation strength reading の一部として扱う。
例えば、すべての重みが正で値域が nonnegative なら、

```text
K(A) = 0 -> forall i, kappa(D_i) = 0
```

を読める。一方、負の値や cancellation を許す aggregate では、全体の zero から
各 diagram の zero は従わない。

## スコープ

この PRD のスコープは次である。

- ArchSig v0.3.0 を measurement expansion release として定義する要求。
- AAT 数学本文から追加できる measurement coordinate の選定。
- Atom support / axis restriction measurement。
- Atom compatibility / conflict measurement。
- Observation non-injectivity / reconstruction loss measurement。
- Law universe coverage / witness exactness measurement。
- Feature Extension Formula axes measurement。
- Operation calculus law axes measurement。
- Path signature trajectory measurement。
- Homotopy / operation-order sensitivity measurement。
- Diagram fillability measurement。
- Representation Strength safety measurement。
- 各 measurement が theorem proof、global truth、single quality score、automatic repair safety では
  ないことの boundary。

v0.3.0 の実装設計で具体化するものは次である。

- `archsig-analysis-packet-v0` へ追加する reading families。
- schema field 名と validation rule。
- minimal fixture と expressiveness fixture。
- `docs/tool/archsig_analysis_packet.md` の packet 説明更新。
- ArchSig / FieldSig handoff で current-state measurement と evolution analysis を混同しないための
  downstream boundary。

## Non-Goals

この PRD は次を目標にしない。

- ArchSig を合否判定器、static lint、single architecture quality score にする。
- tool quality、CLI UX、summary UX、review UX を v0.3.0 の主目的にする。
- sharded ArchMap authoring、bundle/export workflow、大規模 repo authoring ergonomics を完成させる。
- release assets、skills packaging、installation flow の完成度を主目的にする。
- PR / diff / change-vector evolution を ArchSig の責務にする。
- FieldSig の forecast、governance、calibration、operational feedback を再設計する。
- LLM observation を canonical Atom truth として扱う。
- ArchSig が source extraction completeness、semantic correctness、global architecture truth、
  architecture lawfulness、zero curvature、Lean theorem discharge を証明する。
- Feature Extension Formula axes から actual feature PR の安全性を結論する。
- Operation calculus law axes から operation theorem を無条件に導く。
- Path signature trajectory から実 repository evolution の future trajectory を予測する。
- Homotopy reading から全 operation order の可換性を結論する。
- Diagram fillability reading から全 split / repair / extension failure を diagram failure へ還元する。
- Representation Strength reading から analytic value が architecture object 全体を復元すると結論する。
- Aggregate zero から local zero を無条件に結論する。

## Acceptance Criteria / 完了条件

- v0.3.0 が Measurement Expansion Release であり、tool quality や review UX は v0.7.0 以降へ
  回す方針が明記されている。
- v0.3.0 の優先順位が、新しい AAT measurement coordinate、claim boundary、schema / fixture
  reproducibility、review workflow polish、packaging / release UX の順で定義されている。
- Atom support / axis restriction が、support size、axis restriction counts、axis concentration、
  mixed-axis molecule pressure として要求されている。
- Atom compatibility / conflict が、same-slot conflict、payload inconsistency、compatibility status として
  要求されている。
- Observation non-injectivity / reconstruction loss が、observation collision、collapsed atom family、
  hidden atom family、reconstruction blocker として要求されている。
- Law universe coverage / witness exactness が、required law coverage、witness family coverage、
  signature axis coverage、exactness assumption status として要求されている。
- Feature Extension Formula axes が、inherited core obstruction、feature-local obstruction、
  interaction obstruction、lifting failure、filling failure、complexity transfer、residual coverage gap として
  要求されている。
- Operation calculus law axes が、composition、associativity under observation、
  refinement / abstraction compatibility、protection idempotence、runtime localization、
  migration compatibility、repair monotonicity などとして要求されている。
- Path signature trajectory が、endpoint delta、max axis excursion、non-monotone axis refs、
  path cost proxy、introduced obstruction trajectory として要求されている。
- Homotopy / operation-order sensitivity が、independent square、same-contract replacement、
  operation order sensitivity、homotopy blockers として要求されている。
- Diagram fillability が、missing filler kind、filler candidates、non-fillability witnesses、
  filling blockers として要求されている。
- Representation Strength safety が、ZeroPreserving、ZeroReflecting、
  ObstructionPreserving、ObstructionReflecting、required assumptions、
  blocked reflection / preservation reason として要求されている。
- 各 measurement が source refs、observation refs、coverage boundary、non-conclusions を保持することが
  要求されている。
- Non-Goals が、single score 化、tool polish、PR / diff evolution、FieldSig 再設計、LLM truth、
  theorem discharge、automatic repair safety を明確に除外している。
