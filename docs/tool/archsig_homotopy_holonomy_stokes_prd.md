# ArchSig Homotopy / Holonomy Stokes PRD

この PRD は、AAT Homotopy-Holonomy Stokes Theorem を ArchSig の
実用計測面として追加するための要求を定義する。

中心方針は次である。

```text
LLM-native ArchSig measurement
  > architectural holes and filler evidence
  > bounded Stokes-style theorem support
  > minimal Lean guardrail
  > AAT / tool / website documentation alignment
```

この PRD では、Lean で完全な homotopy / homology / Stokes 理論を形式化することを
主目的にしない。ArchSig が supplied ArchMap、LawPolicy、analysis packet から、
codebase 上の path pair、loop、filler、unfilled hole、nonzero holonomy を測定し、
一般の engineer と LLM agent が読める architecture diagnosis を出すことを第一の目的にする。

既存の [ArchSig Monodromy / Boundary Holonomy Measurement PRD](archsig_monodromy_boundary_holonomy_prd.md)
は、operation square、path continuation trace、boundary holonomy、feature extension diagnosis を
主に扱う。この PRD はそれを置き換えない。今回の主対象は、codebase 全体を
selected homotopy complex として読み、loop が戻らない理由を local curvature と
architectural hole に分けることである。

ArchSig の出力は、次の形の bounded diagnosis として読む。

```text
ArchSig measured selected path loops, fillers, holes, and holonomy
under recorded LawPolicy, coverage, continuation, distance, and exactness assumptions.
```

これは architecture lawfulness、global semantic flatness、future safety、
Lean theorem discharge、source extraction completeness を結論するものではない。

## 要求

### R0. LLM-native ArchSig 計測を最優先にする

ArchSig は、homotopy / holonomy / Stokes reading を数学的 decoration ではなく、
LLM が叩いて codebase inspection を進めるための計測面として扱わなければならない。

優先する問いは次である。

```text
同じ意味に到達するはずの複数 path は、本当に同じ selected observation に戻るか。
その同一性を支える contract / law / test / runtime evidence / semantic evidence はあるか。
loop が戻らない場合、それは埋められる loop 内部の local curvature か。
それとも filler がない architectural hole か。
```

ArchSig は、少なくとも次を出力できなければならない。

- selected LawPolicy refs
- selected axes
- homotopy complex summary
- measured path pairs
- measured loops
- filled loops
- unfilled loops
- filler candidates
- missing filler evidence
- nonzero holonomy loops
- top local curvature cells
- architectural hole readings
- loop support localization
- source refs / observation refs
- coverage boundary
- exactness assumption status
- recommended review focus
- non-conclusions

### R1. 一般のエンジニアが得るアウトカムを定義する

この実装により、一般の engineer は次を得られなければならない。

第一に、同じ結果へ行く複数経路が本当に同じ意味を保っているかを確認できる。
例えば repository path と cache path、event projection path と direct read path、
interface path と implementation path、old schema path と new schema path を比較し、
selected semantic / state / effect / authority axis で戻っているかを読める。

第二に、違反と断言できないが設計証拠が欠けている領域を見つけられる。
ArchSig は、loop が存在するが filler がない場合、それを violation ではなく
architectural hole として出す。
これにより、engineer は「この二経路は同じはず」という暗黙知に対して、
contract、test、runtime guarantee、semantic equivalence、authority proof があるかを確認できる。

第三に、戻らない loop の原因を local curvature と missing filler に分けられる。
埋められる loop の holonomy が非ゼロなら、内部の law cell に selected local curvature がある。
埋められない loop なら、まず filler evidence が不足している。
この区別により、bug fix、contract 明文化、test 追加、boundary 設計、runtime evidence 収集の
どれへ進むべきかを選びやすくなる。

第四に、eventual consistency、cache freshness、retry idempotency、authorization bypass、
serialization roundtrip のような問題を静的依存とは別軸で読める。
static dependency graph が acyclic でも、semantic / state / runtime / effect / authority の
空間には loop と hole が残りうる。

第五に、レビュー説明が traceable になる。
ArchSig は、path pair、loop、filler candidate、missing evidence、source refs、
observation refs、coverage status を report に残す。
これにより、reviewer は「この設計は曖昧」ではなく、
「この cache / repository loop は selected semantic axis で nonzero holonomy を持ち、
projection freshness filler が missing」と説明できる。

第六に、LLM agent が次の調査を進めやすくなる。
Report は、人間向けの巨大証明ではなく、LLM が source refs を再確認し、
missing filler を探し、LawPolicy の unresolved question を整理し、
ArchSig を再実行できる structured reading として設計する。

### R2. Homotopy reading を LLM-native skill flow に組み込む

Homotopy / Stokes 用の LawPolicy、measurement profile、path discovery rule は、
人間が詳細設計して書く artifact ではない。
LLM agent が `tools/archsig/skills` を使って構成、検証、読み取りを行う。

Primary flow は次である。

```text
human intent
  -> tools/archsig/skills/archmap-creater
  -> tools/archsig/skills/law-policy-creater
  -> ArchSig validation
  -> tools/archsig/skills/archsig-reader
  -> bounded homotopy / holonomy reading
```

人間が指定するのは、policy 詳細ではなく次の意図と制約である。

- analysis goal: codebase inspection, migration review, cache consistency review, event flow review
- risk focus: semantic equivalence, state/effect ordering, retry idempotency, authority, serialization, projection freshness
- source scope: repository, subsystem, feature, service, package
- normative evidence: architecture docs, coding standards, ADR, review policy, direct user decision
- excluded readings and private / unavailable evidence
- how conservative the zero / filler reading should be

LLM は selected law を発明してはならない。
Normative source または user decision がない同一性主張は、selected law ではなく
question、optional reading、unfilled loop、coverage gap、excluded reading として残す。

### R3. Architecture Homotopy Complex を bounded report reading として作る

ArchSig は、supplied ArchMap と LawPolicy から selected architecture homotopy complex
summary を構成できなければならない。

最小の reading は次を持つ。

- `0-cells`: component, operation, state, effect, event, contract, semantic object, resource, authority scope
- `1-cells`: call, read, write, emit, handle, authorize, project, substitute, serialize, deserialize, retry, compensate, migrate, calculate
- `2-cells`: law witness, contract filler, commutative square, substitution square, projection square, state/effect ordering square, retry idempotency square, authorization square, semantic calculation square

この complex は source truth ではない。
ArchMap observations、LawPolicy、LLM-discovered candidates、coverage boundary から作る
bounded analysis object である。

### R4. Path pair と loop candidate を列挙する

ArchSig は、同じ endpoint を持つ candidate path pair を列挙できなければならない。

最小の path source は次である。

- calculation path
- state transition path
- event projection path
- authorization path
- serialization roundtrip
- retry / effect path
- interface / implementation path
- cache / repository path
- migration old / new path

Candidate は少なくとも次を区別する。

- LLM-discovered candidate
- LawPolicy-required candidate
- ArchMap-supplied candidate
- source-confirmed candidate
- unresolved / needsReview candidate

Candidate は review cue であり、path truth ではない。

### R5. Filler candidate と architectural hole を分ける

ArchSig は、各 loop について filler candidate を探し、filled / unfilled を区別できなければならない。

Filler candidate は少なくとも次を含む。

- contract
- test
- type refinement
- schema invariant
- idempotency evidence
- authorization policy
- event ordering guarantee
- transaction boundary
- compensation law
- domain invariant
- runtime observation
- semantic equivalence note

Filler がない loop は violation ではなく `architectural hole` として出す。
Report は、missing filler evidence と、追加確認すべき source refs / docs refs / runtime refs を示す。

### R6. Homotopy holonomy を selected axis ごとに計測する

ArchSig は、path `p` と `q` の selected continuation trace を axis ごとに比較できなければならない。

```text
Hol_x(p, q)
  = distance_x(Cont_x(p), Cont_x(q))
```

扱う axis は少なくとも次を含む。

- static / support
- contract
- semantic
- state
- effect
- authority / trust
- runtime
- projection / representation

各 holonomy reading は次を持つ。

- path pair refs
- loop ref
- axis id
- distance kind
- value
- compared continuation summary
- source refs / observation refs
- filler refs or missing filler refs
- coverage boundary
- exactness assumption status
- non-conclusions

### R7. Discrete Stokes reading を report する

ArchSig は、measured filling `S` がある loop について、bounded Stokes-style reading を出せなければならない。

```text
Hol_x(boundary(S))
  <= sum local curvature cells in S
```

Tool report では、これを theorem proof ではなく、次の review logic として使う。

```text
filled loop has nonzero holonomy
  -> inspect local curvature cells in its measured filling

loop has no filler
  -> report architectural hole and missing evidence
```

ArchSig は、measured filling がない loop について、内部 local curvature を結論してはならない。
その場合は unfilled loop / architectural hole として扱う。

### R8. Architecture Homotopy Report を追加する

ArchSig は、homotopy / holonomy / filler reading をまとめた
`ArchitectureHomotopyReport` を出力できなければならない。

Report は少なくとも次を含む。

- schema version
- selected LawPolicy ref
- ArchMap / analysis packet refs
- selected axes
- homotopy complex summary
- measured path pair summary
- measured loop summary
- filled loops
- unfilled loops
- nonzero holonomy loops
- top local curvature cells
- missing filler evidence
- architectural hole readings
- optional `beta1` / hole rank reading when bounded chain data is available
- optional `HolMass`, `FillRatio`, `CurvedFillMass`, `HoleHolonomy` aggregate readings
- recommended review focus
- non-conclusions

Aggregate readings are not single architecture quality scores.
They are review prioritization readings and must carry coverage / exactness / selected-axis boundaries.

### R9. Codebase inspection を primary use case にする

この surface の primary use case は PR diff review ではなく、repository / codebase 全体の
architecture health scan である。

ArchSig は、次を読めるようにする。

- cache / repository alternative path の semantic loop
- event projection / direct read consistency loop
- retry / effect idempotency loop
- authorization bypass style loop
- interface / implementation contract loop
- serialization / deserialization roundtrip loop
- migration old / new schema roundtrip loop
- calculation ordering loop

PR review へ展開する場合も、raw diff ではなく ArchMap / ArchMapDelta / LawPolicy に基づく
bounded diagnosis として扱う。

### R10. Lean 形式化は minimal guardrail に絞る

Lean 側では、ArchSig implementation の完全性や一般 homology 理論を証明しない。
必要な範囲の guardrail と theorem boundary を追加する。

Lean で扱う候補は次である。

- finite measured path / loop / 2-cell family
- selected continuation function
- local curvature for measured 2-cell boundary paths
- holonomy for measured path pair
- compositional continuation assumptions
- triangle inequality / subadditivity assumptions
- bounded Stokes inequality for measured filling
- nonzero boundary holonomy implies at least one nonzero measured local curvature under filling
- unfilled loop is not a violation conclusion
- non-conclusions theorem package / schema

Lean は、semantic correctness、LawPolicy authoring correctness、
ArchSig implementation correctness、global homotopy completeness、future safety を証明しない。

### R11. AAT 数学本文と関連 docs を更新する

実装時には、AAT / tool / website の説明面を同期する。

更新対象は少なくとも次を含む。

- AAT 数学本文: path / homotopy / diagram filling / holonomy / Stokes-style reading の位置づけ
- `docs/aat/proof_obligations.md`: Lean で支える範囲、future proof obligation、empirical hypothesis
- `docs/aat/lean_theorem_index.md`: 追加した Lean definition / theorem / non-conclusion
- `docs/tool/README.md`: Homotopy report の位置づけ
- `docs/tool/law_policy.md`: homotopy / filler / loop measurement policy
- `docs/tool/archsig_analysis_packet.md`: ArchitectureHomotopyReport の読み方
- `tools/archsig/skills/law-policy-creater`: homotopy measurement profile の LLM-native 構成
- `tools/archsig/skills/archsig-reader`: ArchitectureHomotopyReport の LLM-native 読み取り
- website / public manual: public surface に出す場合の reading guide

AAT 数学本文では、tool implementation status、Issue 番号、fixture 詳細を混ぜない。
tool docs では、AAT theorem と ArchSig report reading を混同しない。

### R12. Non-conclusions を report と docs に残す

ArchSig は、homotopy report に次の non-conclusions を必ず含める。

- Homotopy report は architecture object の全構造を復元しない
- unmeasured path は flat / equivalent ではない
- missing filler は violation proof ではない
- unfilled loop は architectural hole reading であり defect absence でも defect proof でもない
- nonzero holonomy は selected-axis observation difference であり future incident proof ではない
- filled loop の nonzero holonomy から local curvature を読むには measured filling と assumptions が必要
- `beta1` / hole rank reading は selected measured complex に相対化される
- ArchSig report は Lean theorem discharge ではない

### R13. Validation fixture を用意する

ArchSig は、最小 fixture で ArchitectureHomotopyReport を安定して出力できなければならない。

必要な fixture は次である。

- zero holonomy filled loop fixture
- nonzero holonomy filled loop fixture
- unfilled architectural hole fixture
- cache / repository semantic loop fixture
- event projection / direct read consistency fixture
- retry / idempotency effect fixture
- authorization bypass hole fixture
- coupon / tax / rounding semantic loop fixture

Validation は schema shape、non-conclusions、coverage boundary、path refs、
filler refs、missing filler refs、holonomy refs、local curvature refs を確認する。
Validation は architecture lawfulness や Lean theorem discharge を証明しない。

## スコープ

この PRD のスコープ内:

- ArchSig analysis packet に ArchitectureHomotopyReport を追加する。
- finite measured path pair / loop / filler family から homotopy reading を出す。
- filled loop と unfilled loop を分離する。
- nonzero holonomy と missing filler evidence を report に出す。
- measured filling がある loop について Stokes-style review reading を出す。
- optional aggregate reading として `beta1`, `HolMass`, `FillRatio`, `CurvedFillMass`, `HoleHolonomy` を扱う。
- codebase inspection surface で homotopy report を読めるようにする。
- `tools/archsig/skills/law-policy-creater` が homotopy measurement profile を LLM-native に構成できるようにする。
- `tools/archsig/skills/archsig-reader` が ArchitectureHomotopyReport を読めるようにする。
- Lean 側に minimal theorem guardrail を追加する。
- AAT 数学本文、AAT proof obligation / theorem index、tool docs、必要な website surface を同期する。

この PRD のスコープ外:

- ArchMap を law-relative artifact に変更する。
- ArchSig を Lean 証明器にする。
- raw source から完全な cell complex を自動抽出する。
- PR diff / FieldSig longitudinal forecast を HomotopyReport だけで置き換える。
- 完全な sheaf / Hodge / homology library を最初から実装する。
- empirical incident risk、review cost、future safety の calibration をこの PRD で完了する。

## Non-Goals

- Homotopy report を単一の architecture quality score にすること。
- selected measured complex の `beta1` を repository 全体の真の topology として扱うこと。
- unfilled loop を無条件に violation として扱うこと。
- missing evidence を defect absence として扱うこと。
- nonzero holonomy から unmeasured axes の obstruction を結論すること。
- filled loop でないものに Stokes-style local curvature conclusion を出すこと。
- ArchMap に filler conclusion、homology rank、holonomy judgement、flatness judgement を保存すること。
- 一般の engineer に law / witness / distance / exactness / chain complex の詳細設計を要求すること。
- LLM が source evidence や user decision なしに selected law / filler law を発明すること。
- Lean で ArchSig implementation correctness を証明したり、source-observation layer の性質を AAT theorem として扱うこと。
- AAT 数学本文に tool の実装状況、fixture、CLI 詳細を混ぜること。

## Acceptance Criteria / 完了条件

- ArchitectureHomotopyReport が schema として表現できる。
- ArchSig が supplied ArchMap + LawPolicy から ArchitectureHomotopyReport を生成できる。
- Report に selected axes、path pairs、loops、filled loops、unfilled loops、filler candidates、
  nonzero holonomy loops、top local curvature cells、missing filler evidence、non-conclusions が含まれる。
- Report から、同じ意味へ行く複数 path の selected-axis 差、architectural hole、
  missing filler、local curvature candidate、次の action を読める。
- ACTS / spectrum report とは別に、homotopy / filler / hole / Stokes-style reading として責務が分かれている。
- Part IV Distance Engine integration では、`homotopyDistanceReadings[]` が
  selected loop / path pair から homotopy distance、filling cost、
  observation gap lower bound、selected finite Dehn-style area を生成し、
  missing filler evidence は zero filling cost ではなく blocker として保持する。
  loop / filler / hole / holonomy / Stokes / report surface は `part4DistanceRefs` を持つ。
- `tools/archsig/skills/law-policy-creater` が homotopy measurement profile を
  human intent、repository evidence、ArchMap から LLM-native に構成できる。
- `tools/archsig/skills/archsig-reader` が ArchitectureHomotopyReport を読み、
  LLM が bounded architecture reading と next action を説明できる。
- 一般の engineer は chain complex、homology、distance、exactness の詳細を設計せず、
  analysis goal、risk focus、source scope、normative evidence、除外条件を指定すればよい。
- Filled loop の nonzero holonomy reading は、measured filling と Stokes-style assumptions に限定される。
- Unfilled loop は violation proof ではなく architectural hole と missing filler evidence として出る。
- zero holonomy fixture、nonzero holonomy filled loop fixture、unfilled hole fixture、
  cache / repository fixture、event projection fixture、retry / idempotency fixture、
  authorization fixture が追加される。
- ArchSig validation test が schema shape、refs、coverage boundary、non-conclusions を確認する。
- Lean 側に minimal theorem guardrail が追加され、`lake build` が通る。
- `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` が Lean 追加分と claim boundary を反映する。
- AAT 数学本文が Homotopy-Holonomy Stokes の位置づけを、実装状況ではなく理論的 reading として反映する。
- `docs/tool/README.md`、`docs/tool/law_policy.md`、`docs/tool/archsig_analysis_packet.md` が HomotopyReport を説明する。
- public website / manual に出す場合は、homotopy report の読み方と non-conclusions が同期される。
- `cargo test --manifest-path tools/archsig/Cargo.toml` が通る。
- Lean 変更を含む場合は `lake build` が通る。
- `git diff --check` と hidden / bidirectional Unicode scan が通る。
