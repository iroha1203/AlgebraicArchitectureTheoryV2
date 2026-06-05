# ArchSig Monodromy / Boundary Holonomy Measurement PRD

この PRD は、ArchSig に path monodromy と boundary holonomy の実用計測面を追加するための要求を定義する。

中心方針は次である。

```text
practical ArchSig measurement
  > bounded claim boundary
  > minimal Lean guardrail
  > AAT mathematical exposition
  > later workflow polish
```

この PRD では、Lean で完全な monodromy 理論を証明することを主目的にしない。
ArchSig が実 repository / supplied ArchMap / LawPolicy / analysis packet から、変更順序、
feature boundary、semantic / state / effect / authority の交換不能性を実用的に読めることを
第一の目的にする。

ArchSig の出力は、次の形の bounded diagnosis として読む。

```text
ArchSig detected nonzero measured monodromy
on selected axes under recorded coverage and exactness assumptions.
```

これは architecture lawfulness、global safety、future correctness、Lean theorem discharge を
結論するものではない。

## 要求

### R0. ArchSig の実用計測を最優先にする

ArchSig は、path monodromy と boundary holonomy を theoretical decoration ではなく、
review / design diagnosis に使える測定面として扱わなければならない。

優先する問いは次である。

```text
この二つの operation は順序を入れ替えても同じ architecture reading を保つか。
この feature extension は core / feature boundary で semantic, state, effect, authority を戻せるか。
この obstruction は core 内部、feature 内部、境界、coverage gap のどこに局在するか。
```

ArchSig は、少なくとも次を出力できなければならない。

- measured operation pair
- compared path pair
- selected axes
- axis-wise defect
- aggregate monodromy index
- affected Atom / molecule / component / boundary refs
- source refs / observation refs
- coverage status
- exactness assumption status
- top nonzero measured squares
- suggested filler / lifting / boundary evidence
- non-conclusions

### R1. 現場アウトカムを定義する

この実装により、現場のエンジニアは次を得られなければならない。

第一に、変更順序の危険を merge 前に読めるようになる。
ArchSig は、二つの operation を入れ替えたときに semantic、state、effect、authority の
読みが変わる箇所を、operation-order sensitivity として示す。
これにより、engineer は「単独では安全に見える二つの変更」が組み合わさると壊れるケースを
PR review や設計レビューで早く見つけられる。

第二に、feature extension の調査範囲を core、feature、boundary、coverage gap に分けられる。
障害や設計劣化が起きたとき、ArchSig は全体を漠然と疑うのではなく、core-local、
feature-local、boundary holonomy、lifting failure、filling failure、residual coverage gap の
どこに measured witness があるかを示す。
これにより、debug / review / refactoring の焦点を絞れる。

第三に、static dependency graph では見えにくい semantic / runtime / state / effect の
交換不能性を review surface に出せる。
循環がない、layering が綺麗、final component set が同じ、という粗い観測だけでは見落とす
coupon / tax / rounding、payment / receipt、authorization / trust boundary のようなズレを、
axis-wise defect と witness refs で読めるようにする。

第四に、review comment を主観的な違和感から traceable evidence へ変える。
ArchSig は、nonzero monodromy witness に source refs、observation refs、affected Atom refs、
law / signature refs、missing evidence を付ける。
これにより、reviewer は「この変更は危険そう」ではなく、
「この operation pair は selected semantic axis でこの witness により交換不能に見える」と
説明できる。

第五に、設計判断の next action を明確にする。
ArchSig は automatic repair を出すのではなく、filler、lifting evidence、boundary contract、
coverage 追加、semantic witness 追加など、次に確認すべき証拠を recommended review focus として
提示する。
これにより、engineer は調査を止めずに次の設計作業へ進める。

第六に、tool の結論を過大評価しないための境界も同時に得る。
ArchSig は coverage status、exactness assumption status、non-conclusions を report に含める。
これにより、測定された危険、未測定の危険、証明していない安全性を区別できる。

このアウトカムは、二つの利用形態に分けて提供する。
現時点の ArchSig surface には `PR review mode` はまだ存在しない。
この PRD では、FieldSig が担う本格的な PR / diff / change-vector evolution analysis とは別に、
ArchSig 単体でも使える軽量な PR review mode を追加候補として定義する。

`PR review mode` の canonical input は raw diff ではなく、base ArchMap、
PR-local ArchMap delta、LawPolicy である。LawPolicy なしでは ArchSig judgement を出さない。
semantic、state、effect、authority、runtime の reading は言語別 adapter、extractor、
LLM reader、または manual authoring が供給した ArchMap-level evidence から読む。

```text
PR review mode
  = change-local diagnosis

codebase inspection mode
  = current-state architectural diagnosis
```

`PR review mode` では、base ArchMap と PR-local ArchMapDelta と LawPolicy から、
operation pair、feature boundary、touched Atom support を優先して読む。
目的は、merge 前に operation-order sensitivity、boundary holonomy、missing filler /
lifting evidence、coverage gap を reviewer に示すことである。
この mode は merge safety を結論しないが、reviewer が確認すべき measured witness と
next action を提示する。
この mode は、FieldSig の forecast、governance、calibration、operational feedback、
change-vector evolution を置き換えない。
FieldSig ほど大きな evolution analysis が不要で、PR review のための bounded AAT diagnosis だけを
欲しい利用者のための lightweight surface とする。

`codebase inspection mode` では、現在の repository / ArchMap / analysis packet 全体を、
latest ArchMapSnapshot、ArchMapIndex、必要なら recent delta window から読む。
既存の subsystem boundary、feature-like cluster、operation-like relation、semantic / state /
effect / authority interaction を scan する。
目的は、どの boundary に measured residual obstruction が溜まっているか、どの subsystem pair や
operation square が order-sensitive に見えるかを、architecture health review の材料として示す
ことである。
この mode は repository 全体の lawfulness や global safety を結論しない。

### R2. Operation square candidate を列挙する

ArchSig は、supplied ArchMap と selected LawPolicy から、測定対象となる operation square
candidate を列挙できなければならない。

candidate は次のような operation pair から作る。

```text
f : A -> A_f
g : A -> A_g

p = g . f
q = f . g
```

candidate source は少なくとも次を含む。

- shared Atom support に触る operation pair
- 同じ state subject を read / write する operation pair
- 同じ effect family を発生させる operation pair
- 同じ contract / semantic Atom に触る operation pair
- 同じ authority / trust boundary を横断する operation pair
- feature extension と repair / migration / substitution の operation pair
- ArchMap / analysis packet が明示的に supplied operation pair として持つもの

ArchSig は、operation pair を自動推定した場合と、入力で明示された場合を区別して記録する。
自動推定は review cue であり、operation truth ではない。

### R3. Path continuation trace を axis ごとに記録する

ArchSig は、各 candidate square について、二つの path の selected continuation trace を
axis ごとに記録できなければならない。

少なくとも次の axis family を扱う。

- static dependency / support axis
- contract axis
- semantic axis
- state transition axis
- effect ordering / replay / compensation axis
- authority / trust boundary axis
- runtime interaction axis
- projection / representation axis

trace は、完全な実行意味論ではなく、bounded observation trace として扱う。
ArchSig は trace に source refs、observation refs、derived refs、missing refs を付ける。

### R4. Axis-wise monodromy defect を計測する

ArchSig は、operation square `sigma` と axis `x` に対して、次の形の defect を計測できなければ
ならない。

```text
mu_x(sigma)
  = distance_x(Cont_x(g . f), Cont_x(f . g))
```

`distance_x` は axis ごとの bounded distance でよい。

例:

- boolean mismatch
- mismatch count
- set symmetric difference size
- ordered trace edit distance
- semantic witness mismatch count
- state transition mismatch count
- effect replay mismatch count
- authorization mismatch count
- projection loss / reflection blocker count

各 `mu_x` は、値だけでなく、次を持つ。

- unit / distance kind
- measured support
- compared observations
- positive witness refs
- missing witness refs
- coverage boundary
- exactness assumption status

### R5. Architecture Monodromy Index を aggregate reading として出す

ArchSig は、finite measured square family 上で aggregate reading を出せなければならない。

```text
AMI_X(A)
  = sum_{sigma in measured squares}
    sum_{x in selected axes}
      weight_{sigma,x} * mu_x(sigma)
```

この `AMI_X(A)` は、single quality score ではない。
review prioritization のための aggregate reading であり、次を必ず併記する。

- selected square family
- selected axis family
- weight policy
- zero-reflection assumptions
- cancellation がないことの前提
- top contributors
- aggregate-to-local reading boundary

ArchSig は、`AMI_X(A) = 0` から global path flatness、global homotopy completeness、
future safety を結論してはならない。

### R6. Nonzero monodromy witness を review surface にする

ArchSig は、`mu_x(sigma) > 0` の measured witness を review で読める形にする。

各 witness は少なくとも次を持つ。

- operation pair id
- path `p = g . f`
- path `q = f . g`
- axis id
- defect value
- compared trace summary
- affected Atom refs
- affected law / signature axis refs
- source refs
- observation refs
- suggested filler / lifting / boundary evidence
- recommended review focus
- non-conclusions

recommended review focus は命令ではなく cue として扱う。
ArchSig は automatic repair safety や merge safety を結論しない。

### R7. Boundary holonomy を feature extension reading として出す

ArchSig は、feature extension `ext_f : A -> B` について、core / feature boundary に局在する
measured residual obstruction を boundary holonomy reading として出せなければならない。

境界は次の混合 subconfiguration として読む。

```text
Boundary(A, f)
  = core Atom と feature Atom のあいだの
    relation / capability use / contract refinement /
    state read-write / effect ordering / authority /
    runtime interaction / semantic interpretation
```

出力する boundary holonomy axes は少なくとも次を含む。

- `Hol_static`
- `Hol_contract`
- `Hol_semantic`
- `Hol_state`
- `Hol_effect`
- `Hol_authority`
- `Hol_runtime`
- `Hol_projection`

ArchSig は、boundary holonomy を次の residual diagnosis として扱う。

```text
new measured residual obstruction
  after accounting for core-local and feature-local readings
```

これは、`Ob(B)` が `Ob(A) + Ob(f) + Hol(Boundary(A,f))` に無条件に直和分解するという
主張ではない。support separation、coverage、exactness、residual attribution policy を
明示した範囲での reading とする。

### R8. Feature extension diagnosis を実務的に分解する

ArchSig は、feature extension の measured obstruction を次に分解して報告できなければならない。

- inherited core obstruction
- feature-local obstruction
- boundary holonomy
- lifting failure
- filling failure
- complexity transfer
- residual coverage gap

この分解は、mutually disjoint な theorem decomposition ではない。
同じ witness が複数分類を持つ場合、ArchSig は multi-label attribution として記録する。

### R9. Coupon / tax / rounding fixture を最小実例にする

ArchSig は、coupon / tax / rounding の実例で nonzero semantic monodromy を表現できなければ
ならない。

最小例は次を含む。

```text
f = add coupon discount
g = add tax / rounding rule

p = round(tax(discount(subtotal)))
q = round(discount(tax(subtotal)))
```

この fixture では、少なくとも次を出力する。

- `mu_semantic > 0`
- amount / rounding witness
- `PaymentAmount = FinalAmount` または `ReceiptAmount = FinalAmount` への影響
- static projection では見えにくい semantic obstruction reading
- boundary holonomy reading for coupon feature boundary
- coverage / exactness assumptions
- non-conclusions

### R10. Lean 形式化は minimal guardrail に絞る

Lean 側では、ArchSig の全測定仕様を完全証明することを要求しない。
必要なのは、ArchSig report が主張してよい範囲を支える minimal guardrail である。

Lean で優先する形式化は次である。

- measured square
- selected axis
- axis defect
- finite measured square family
- nonnegative weighted aggregate
- aggregate zero から measured local zero を読む補題
- defect nonzero から selected observation difference を読む補題
- selected observation difference から selected homotopy refutation / non-fillability witness へ接続する補題

Lean は次を主張しない。

- 全 operation path の homotopy completeness
- all axes の semantic completeness
- source-observation layer
- global architecture truth
- feature extension safety
- ArchSig measurement correctness in the wild

### R11. AAT 数学本文では証明済み核・予想・tool diagnosis を分離する

AAT 数学本文に取り込む場合、次を分けて書く。

- proved / formalized guardrail
- design-level theorem candidate
- boundary holonomy conjecture
- ArchSig measurement diagnosis
- non-conclusions

`Path-Monodromy Obstruction Theorem` は、Lean で支えた片方向の soundness と、
追加仮定が必要な completeness / equivalence を分ける。

`Boundary Holonomy Conjecture` は、feature extension の中心予想として置く。
ただし、ArchSig 実装はこの予想を証明するものではなく、selected measured axes 上の
boundary holonomy witness を report するものとして扱う。

## スコープ

この PRD のスコープは次である。

- ArchSig に path monodromy measurement を追加する要求。
- ArchSig に boundary holonomy reading を追加する要求。
- 現場エンジニアに提供する実用アウトカム。
- ArchMapStore delta / commit / snapshot / index model を canonical change input として扱う要求。
- PR review mode と codebase inspection mode の分離。
- FieldSig の本格的な evolution analysis と ArchSig の lightweight PR review surface の責務分離。
- ArchSig に lightweight PR review mode を追加する要求。
- operation square candidate の列挙。
- axis-wise continuation trace の記録。
- axis-wise monodromy defect の計測。
- Architecture Monodromy Index の aggregate reading。
- nonzero monodromy witness の review surface。
- feature extension obstruction の boundary-local diagnosis。
- coupon / tax / rounding fixture。
- Lean minimal guardrail の要求。
- AAT 数学本文での証明済み核、予想、tool diagnosis の責務分離。

実装設計で具体化するものは次である。

- `archsig-analysis-packet-v0` へ追加する monodromy / boundary holonomy reading family。
- base ArchMap / PR-local ArchMap delta / LawPolicy を入力として受ける lightweight PR review command または workflow。
- raw diff を PR review input surface から除外する input boundary。
- codebase inspection mode で使う ArchMapSnapshot / ArchMapIndex boundary。
- PR review mode 用の change-local report layout。
- PR review mode で出力する measured witness、recommended review focus、coverage / exactness boundary。
- schema field 名と validation rule。
- LawPolicy 側で必要な selected axes / distance / weight / coverage policy。
- fixture と golden output。
- report 表示。
- docs/tool の packet 説明更新。
- AAT 数学本文との cross-reference。
- Lean theorem index / proof obligations での bounded status 記録。

## Non-Goals

この PRD は次を目標にしない。

- ArchSig を theorem prover にする。
- ArchSig を merge safety 判定器、future safety 判定器、automatic repair system にする。
- `AMI_X(A)` を single architecture quality score にする。
- `AMI_X(A) = 0` から global path flatness や all operation commutativity を結論する。
- `mu_x > 0` から unmeasured axes の obstruction を結論する。
- boundary holonomy から feature extension の安全性または危険性を無条件に結論する。
- core / feature / boundary obstruction が互いに素に分解できることを無条件に主張する。
- supplied ArchMap や LLM observation を canonical architecture truth として扱う。
- source extraction completeness、runtime telemetry completeness、semantic universe completeness を主張する。
- FieldSig の forecast、governance、calibration、operational feedback schema を再設計する。
- FieldSig が担う本格的な PR / diff / change-vector evolution analysis を ArchSig の責務にする。
- ArchSig の lightweight PR review mode から FieldSig の forecast / governance / calibration と同等の
  結論を出す。
- raw diff を semantic / state / effect / authority / runtime reading の canonical input として扱う。
- Lean で完全な monodromy / holonomy 理論を形式化する。
- AAT 数学本文で boundary holonomy を証明済み theorem として扱う。
- UI / report polish、large repository authoring ergonomics、release packaging を主目的にする。

## Acceptance Criteria / 完了条件

- ArchSig の優先順位が、practical measurement、bounded claim boundary、minimal Lean guardrail、
  AAT exposition、later workflow polish の順で定義されている。
- 現場アウトカムが、変更順序の危険検出、feature extension の調査範囲分解、
  static graph では見えにくい semantic / runtime / state / effect の交換不能性検出、
  traceable review evidence、next action cue、coverage / exactness boundary として
  定義されている。
- 利用形態が、base ArchMap / PR-local ArchMap delta / LawPolicy を読む `PR review mode` と、
  repository / ArchMap / analysis packet 全体を ArchMapSnapshot / ArchMapIndex から読む
  `codebase inspection mode` に分離され、それぞれ change-local diagnosis と
  current-state architectural diagnosis として定義されている。
- raw diff は PR review input surface ではなく、canonical semantic input でもないことが明記されている。
- `PR review mode` は現行 ArchSig surface にはまだ存在しない追加要求であり、FieldSig の
  PR / diff / change-vector evolution analysis を置き換えない lightweight surface として
  定義されている。
- ArchSig の lightweight PR review mode が、base ArchMap / PR-local ArchMap delta / LawPolicy を入力し、
  operation-order sensitivity、boundary holonomy、missing filler / lifting evidence、
  coverage gap、non-conclusions を change-local report として出す要求として定義されている。
- operation square candidate が、shared Atom support、state、effect、contract、semantic、
  authority、runtime interaction、supplied operation pair から列挙されることが要求されている。
- path continuation trace が、static、contract、semantic、state、effect、authority、runtime、
  projection axis ごとに記録されることが要求されている。
- axis-wise defect `mu_x(sigma)` が、distance kind、measured support、witness refs、
  coverage boundary、exactness assumption status とともに要求されている。
- `AMI_X(A)` が aggregate review reading であり、single score や global theorem conclusion では
  ないことが明記されている。
- nonzero monodromy witness が、operation pair、path pair、axis、defect value、affected Atom refs、
  law / signature refs、suggested filler / lifting / boundary evidence を持つ review surface として
  要求されている。
- boundary holonomy が、core / feature boundary の measured residual obstruction reading として
  要求されている。
- `analysis-summary.trendDiagnosis.trendInsights` が、path continuation defect と boundary residual
  localization を compact な二次診断として読む。これは packet の axis-wise defect /
  nonzero monodromy witness / feature-boundary residual を交差参照する reading であり、
  same endpoint を homotopy equivalence として扱ったり、boundary holonomy を theorem として
  主張したりしない。
- feature extension diagnosis が、inherited core obstruction、feature-local obstruction、
  boundary holonomy、lifting failure、filling failure、complexity transfer、residual coverage gap の
  multi-label attribution として要求されている。
- coupon / tax / rounding fixture が、semantic monodromy と boundary holonomy の最小実例として
  要求されている。
- Lean 形式化が minimal guardrail に限定され、complete monodromy theory や extractor correctness を
  要求しないことが明記されている。
- AAT 数学本文では、証明済み核、design-level theorem candidate、boundary holonomy conjecture、
  ArchSig measurement diagnosis、non-conclusions を分離することが要求されている。
- Non-Goals が、theorem prover 化、single score 化、global path flatness、automatic safety、
  FieldSig 再設計、完全 Lean 形式化を明確に除外している。
