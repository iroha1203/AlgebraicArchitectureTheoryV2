# ArchSig Curvature / Transfer Spectrum PRD

この PRD は、AAT Curvature-Transfer Spectrum Theorem / ACTS を
ArchSig の実用計測面として追加するための要求を定義する。

中心方針は次である。

```text
ArchSig measurement first
  > bounded AAT theorem support
  > Lean guardrail where useful
  > AAT / tool / website documentation alignment
```

この PRD では、Lean で完全な spectral / transfer 理論を形式化することを
主目的にしない。ArchSig が supplied ArchMap、LawPolicy、analysis packet から、
selected axes 上の curvature support、obstruction transfer、recurrent mode、
review focus を計測できることを第一の目的にする。

ArchSig の出力は、次の形の bounded diagnosis として読む。

```text
ArchSig measured selected-axis curvature and transfer modes
under recorded coverage, distance, weight, and exactness assumptions.
```

これは architecture lawfulness、global flatness、semantic correctness、
future safety、Lean theorem discharge を結論するものではない。

## 要求

### R0. ArchSig で計測できることを最優先にする

ArchSig は、curvature / transfer spectrum を数学的 decoration ではなく、
codebase inspection と design diagnosis に使える計測面として扱わなければならない。

優先する問いは次である。

```text
どの support / axis に nonzero curvature が局在しているか。
どの obstruction が support と axis をまたいで結合しているか。
どの transfer mode が recurrent obstruction として戻ってくるか。
どの coverage gap により zero conclusion を出せないか。
```

ArchSig は、少なくとも次を出力できなければならない。

- selected law universe / LawPolicy refs
- selected axis family
- measured witness family
- distance kind and weight policy
- curvature support operator reading
- transfer operator reading
- top curvature modes
- top transfer / recurrent modes
- witness clusters
- affected Atom / molecule / component / boundary refs
- source refs / observation refs
- coverage boundary
- exactness assumption status
- missing evidence
- recommended review focus
- non-conclusions

### R1. 一般のエンジニアが得るアウトカムを定義する

この実装により、一般のエンジニアは次を得られなければならない。

第一に、巨大な codebase のどこから見ればよいかが分かる。
ArchSig は、violation count や抽象的な health score ではなく、support、axis、
witness cluster、source refs をまとめて、調査すべき architecture hotspot を提示する。
これにより、engineer は「どこかが複雑そう」ではなく、
「semantic / state / effect の nonzero mode がこの subsystem に集中している」と読める。

第二に、静的依存グラフでは見えない設計劣化を見つけられる。
import cycle がない、layering が綺麗、interface 経由で依存している、という状態でも、
semantic contract、state transition、runtime retry、effect idempotency、authority boundary が
ずれていれば、ArchSig は selected-axis curvature として出す。
これにより、engineer は「依存関係は正しいのに動作や意味が壊れる」種類の問題を
architecture review の対象にできる。

第三に、局所的な不具合と構造的な再発パターンを分けられる。
ArchSig は、単発の nonzero witness と、support / axis をまたいで戻ってくる
recurrent obstruction を区別する。
これにより、engineer は一つの TODO を直すべきか、boundary、contract、state / effect policy、
runtime pattern をまとめて見直すべきかを判断しやすくなる。

第四に、レビューや設計相談の説明が traceable になる。
ArchSig は、top mode に affected Atom refs、source refs、witness refs、coverage status、
missing evidence を付ける。
これにより、reviewer は「この設計は危ない気がする」ではなく、
「この witness cluster は selected semantic axis と effect axis で nonzero curvature を持ち、
この source refs に根拠がある」と説明できる。

第五に、測定できた危険と測定できていない危険を分けられる。
ArchSig は、coverage gap、unmeasured axis、exactness assumption status を report に含める。
これにより、engineer は `zero` を安全証明として誤読せず、
「ここは measured zero」「ここは unmeasured」「ここは additional evidence が必要」を
分けて読める。

第六に、次の action が明確になる。
ArchSig は automatic repair を結論しないが、review focus、追加すべき witness、
補うべき semantic contract、確認すべき runtime evidence、分離すべき boundary を提示する。
これにより、engineer は report を読んだ後に、調査、docs 補強、test 追加、contract 明文化、
refactor candidate のどれに進むべきかを選べる。

### R2. LawPolicy に spectrum reading の前提を持たせる

LawPolicy は、curvature / transfer spectrum を読むために必要な選択を
ArchSig へ明示的に渡さなければならない。

LawPolicy が直接宣言するのは、law-relative な前提に限る。

- selected law universe
- selected axes
- required witness rules
- coverage requirement
- exactness assumption status
- excluded readings
- non-conclusions

距離、重み、support projection、transfer edge extraction、mode ranking のような
計測レシピは、LawPolicy root を肥大化させず、同じ `law-policy-v0` artifact 内の
optional `spectrumMeasurementProfile` subobject として持つ。
これは別ファイルを要求しない。必要になった場合だけ、再利用用に外部参照できるようにする。

`spectrumMeasurementProfile` は少なくとも次を持てる。

- measured witness family rule
- distance kind per axis
- weight policy
- support projection rule
- transfer edge rule
- clustering / ranking options
- report focus options

同じ ArchMap は複数の LawPolicy で再分析できる。
同じ LawPolicy 内で複数の `spectrumMeasurementProfile` を比較してもよいが、
profile の差分を law universe の差分として扱ってはならない。
ArchMap は law-independent な observation map に留め、curvature support、
transfer edge、obstruction circuit、flatness judgement を first-class output として持たない。

### R3. Policy composition を LLM-native skill flow にする

ACTS 用 LawPolicy / `spectrumMeasurementProfile` は、人間が内容を設計して
書く artifact ではなく、LLM agent が repository evidence、ArchMap、user goal、
project conventions を読んで構成する intermediate artifact として扱う。

Primary flow は次である。

```text
human intent
  -> tools/archsig/skills/archmap-creater
  -> tools/archsig/skills/law-policy-creater
  -> ArchSig validation
  -> tools/archsig/skills/archsig-reader
  -> bounded architecture reading
```

人間が指定するのは、policy の詳細ではなく、意図と制約である。

- analysis goal: baseline diagnosis, strict review, migration planning, subsystem inspection
- risk focus: semantic contract, state/effect, runtime, authority, provider boundary, dependency direction
- source scope: repository, subsystem, feature, service, package
- normative evidence: architecture docs, coding standards, ADR, review policy, direct user decision
- excluded readings and private / unavailable evidence
- how conservative the zero-reading should be

LLM は `tools/archsig/skills/law-policy-creater` を使って、normative evidence と
user intent から LawPolicy を構成する。LLM は、law、witness、axis、coverage、
exactness、distance、weight、support projection、transfer edge rule を
人間の手作業ではなく skill-guided synthesis として組み立てる。

ただし、LLM は自分の設計嗜好を selected law として昇格してはならない。
Normative source または user decision がない law は、selected law ではなく
question、optional reading、coverage gap、excluded reading として残す。

生成された policy は、少なくとも次を記録する。

- source evidence used
- user intent used
- generated fields
- LLM-inferred fields
- user-confirmed fields
- unresolved questions
- risky defaults
- validation warnings
- non-conclusions

Policy JSON は human editing surface ではなく、LLM / ArchSig の machine-readable
contract である。人間向け surface は、why this law was selected、which source evidence
supports it、which assumptions block zero-reflection、which questions remain、という
explanation である。

ACTS 実装では、`tools/archsig/skills/law-policy-creater` と
`tools/archsig/skills/archsig-reader` を更新し、spectrum measurement profile の構成、
検証、読み取りを LLM が実行できるようにする。

### R4. Curvature support reading を analysis packet に追加する

ArchSig は、measured witness `sigma` と selected axis `x` について、
local curvature value、weight、support incidence を読めなければならない。

最小実装では curvature value は 0 / 1 でよい。
ただし schema は、後続で richer distance を追加できるようにする。

例:

- boolean mismatch
- mismatch count
- edit distance
- semantic witness mismatch count
- contract refinement distance
- state transition distance
- effect replay mismatch count
- authorization mismatch count
- runtime trace distance

ArchSig は、curvature support operator を bounded report reading として出力する。

```text
L^kappa
  = sum weight(sigma, x) * kappa(sigma, x) * support(sigma, x) * support(sigma, x)^T
```

この reading は、support / axis coupling、top eigenmode、top witness cluster を
説明するための report surface である。ArchSig は `Spec(L^kappa) = {0}` だけから
unmeasured axes や global correctness を結論してはならない。

### R5. Transfer spectrum reading を analysis packet に追加する

ArchSig は、state space を `support x axis` として、measured transfer edge を
有限非負 operator として読めなければならない。

```text
T^kappa[(s, x), (t, y)]
  = sum measured transfer defect from (s, x) to (t, y)
```

ArchSig は、transfer edge ごとに次を保持する。

- source support / axis
- target support / axis
- witness refs
- defect value
- weight
- source refs / observation refs
- transfer explanation
- coverage boundary
- non-conclusions

ArchSig は、positive closed walk を recurrent obstruction reading として出力できる。
`rho(T^kappa) > 0` は recurrent mode の存在として読む。
増幅、将来の障害、運用コスト増加を結論する場合は、別の empirical calibration を要求する。

### R6. Architecture Spectrum Report を追加する

ArchSig は、curvature support と transfer spectrum をまとめた
`ArchitectureSpectrumReport` を出力できなければならない。

Report は少なくとも次を含む。

- schema version
- selected LawPolicy ref
- ArchMap / analysis packet refs
- selected axes
- measured witness summary
- distance / weight policy summary
- curvature support summary
- transfer operator summary
- spectral radius reading
- top eigenmodes
- top witness clusters
- recurrent obstruction readings
- coverage gaps
- exactness assumptions
- recommended review focus
- non-conclusions

Report は単一スコアを出してはならない。
必要に応じて aggregate value を出してもよいが、主 surface は
`top modes + witnesses + axes + support + coverage gap` とする。

### R7. Codebase inspection を primary use case にする

ACTS の primary surface は PR diff review ではなく、repository / codebase 全体の
architecture health scan である。

ArchSig は、次を読めるようにする。

- static dependency は acyclic だが semantic / effect / runtime に nonzero mode がある箇所
- interface dependency は正しく見えるが contract refinement が弱い箇所
- retry / timeout はあるが effect idempotency が不足する箇所
- state update と event emission の順序に curvature がある箇所
- authority call と authorized effect がずれている箇所
- semantic / state / effect / runtime / authority をまたぐ recurrent obstruction

PR review surface へ展開する場合も、raw diff ではなく ArchMap / ArchMapDelta /
LawPolicy に基づく bounded diagnosis として扱う。

### R8. Lean 形式化は理論的裏付けとして必要な範囲に絞る

Lean 側では、ArchSig implementation の完全性を証明しない。
必要な範囲の guardrail と theorem boundary を追加する。

Lean で扱う候補は次である。

- finite weighted curvature support aggregate
- positive weight / nonempty support の下で aggregate zero から local curvature zero を戻す bridge
- finite nonnegative transfer relation と positive closed walk の bounded recurrence reading
- `Spec = all zero` を selected measured curvature zero と接続する small theorem package
- non-conclusions を記録する theorem package / schema

Lean は、semantic correctness、LawPolicy authoring correctness、
ArchSig implementation correctness、global semantic flatness、future safety を証明しない。

### R9. AAT 数学本文と関連 docs を更新する

ACTS を実装するときは、AAT / tool / website の説明面を同期する。

更新対象は少なくとも次を含む。

- AAT 数学本文: curvature / analytic representation / spectral reading の位置づけ
- `docs/aat/proof_obligations.md`: Lean で支える範囲、future proof obligation、empirical hypothesis
- `docs/aat/lean_theorem_index.md`: 追加した Lean definition / theorem / non-conclusion
- `docs/tool/README.md`: ArchSig analysis packet における spectrum report の位置づけ
- `docs/tool/law_policy.md`: spectrum measurement policy
- `docs/tool/archsig_analysis_packet.md`: ArchitectureSpectrumReport の読み方
- website / public manual: public surface に出す場合の reading guide

AAT 数学本文では、tool implementation status、Issue 番号、fixture 詳細を混ぜない。
tool docs では、AAT theorem と ArchSig report reading を混同しない。

### R10. Non-conclusions を report と docs に残す

ArchSig は、ACTS report に次の non-conclusions を必ず含める。

- spectrum value は architecture object の全構造を復元しない
- unmeasured axis は zero ではない
- missing evidence は defect absence ではない
- `Spec(L^kappa) = {0}` は coverage / exactness / zero-reflection なしに lawfulness を示さない
- `rho(T^kappa) > 0` は future incident や empirical cost increase を示さない
- top eigenmode は review focus であり、automatic repair conclusion ではない
- ArchSig report は Lean theorem discharge ではない

### R11. Validation fixture を用意する

ArchSig は、最小 fixture で ACTS report を安定して出力できなければならない。

必要な fixture は次である。

- zero curvature support fixture
- nonzero semantic curvature fixture
- transfer cycle fixture
- coverage gap fixture
- coupon / tax / rounding style fixture

Validation は schema shape、non-conclusions、coverage boundary、top mode refs、
transfer edge refs、recurrent mode refs を確認する。
Validation は architecture lawfulness や Lean theorem discharge を証明しない。

## スコープ

この PRD のスコープ内:

- LawPolicy に spectrum measurement policy を追加する。
- ArchSig analysis packet に ArchitectureSpectrumReport を追加する。
- finite measured witness family から curvature support reading を出す。
- finite transfer edge family から recurrent obstruction reading を出す。
- top eigenmode / top witness cluster / recurrent mode / coverage gap を report に出す。
- codebase inspection surface で spectrum report を読めるようにする。
- `tools/archsig/skills/law-policy-creater` が ACTS 用 profile を LLM-native に構成できるようにする。
- `tools/archsig/skills/archsig-reader` が ArchitectureSpectrumReport を読めるようにする。
- Lean 側に minimal theorem guardrail を追加する。
- AAT 数学本文、AAT proof obligation / theorem index、tool docs、必要な website surface を同期する。

この PRD のスコープ外:

- ArchMap を law-relative artifact に変更する。
- ArchSig を Lean 証明器にする。
- raw source から完全な Atom / witness universe を自動抽出する。
- PR diff / FieldSig longitudinal forecast を ACTS だけで置き換える。
- 完全な sheaf / Hodge Laplacian 理論を最初から実装する。
- empirical incident risk、review cost、future safety の calibration をこの PRD で完了する。

## Non-Goals

- ACTS report を単一の architecture quality score にすること。
- `Spec(L^kappa) = {0}` から無条件に global flatness / global lawfulness を結論すること。
- `rho(T^kappa) > 0` から無条件に障害発生、品質劣化、コスト増を結論すること。
- unmeasured semantic / runtime / authority axis を measured zero として扱うこと。
- coverage gap を absence of defect として扱うこと。
- ArchMap に obstruction circuit、curvature support、transfer edge、flatness judgement を保存すること。
- Lean で ArchSig implementation correctness を証明したり、source-observation layer の性質を AAT theorem として扱うこと。
- AAT 数学本文に tool の実装状況、fixture、CLI 詳細を混ぜること。
- 一般の engineer に law / witness / distance / exactness の詳細設計を要求すること。
- Generic preset を project-specific architectural diagnosis として扱うこと。
- LLM が source evidence や user decision なしに selected law を発明すること。

## Acceptance Criteria / 完了条件

- LawPolicy が spectrum measurement policy を表現できる。
- ACTS 用 LawPolicy / `spectrumMeasurementProfile` は、
  `tools/archsig/skills/law-policy-creater` が human intent、repository evidence、ArchMap から
  LLM-native に構成できる。
- 一般の engineer は law / witness / distance / exactness の詳細を設計せず、
  analysis goal、risk focus、source scope、normative evidence、除外条件を指定すればよい。
- Generated policy に source evidence、user intent、LLM-inferred fields、user-confirmed fields、
  unresolved questions、validation warnings、non-conclusions が記録される。
- `tools/archsig/skills/archsig-reader` が ArchitectureSpectrumReport を読み、
  LLM が bounded architecture reading と next action を説明できる。
- ArchSig が supplied ArchMap + LawPolicy から ArchitectureSpectrumReport を生成できる。
- Report に selected axes、witness family、distance / weight policy、curvature support summary、
  transfer summary、top modes、witness clusters、coverage gaps、non-conclusions が含まれる。
- Report から、hotspot、静的依存では見えない設計劣化、recurrent obstruction、
  traceable review explanation、測定境界、次の action を読める。
- Report は単一スコアではなく、review focus と traceable refs を primary surface にする。
- `Spec(L^kappa) = {0}` の reading は coverage / exactness / zero-reflection 前提つきに限定される。
- `rho(T^kappa) > 0` の reading は recurrent obstruction に限定され、empirical amplification は結論しない。
- zero fixture、nonzero curvature fixture、transfer cycle fixture、coverage gap fixture が追加される。
- ArchSig validation test が schema shape、refs、coverage boundary、non-conclusions を確認する。
- Part IV Distance Engine integration では、`obstructionMeasureReadings[]` と
  `curvatureMassReadings[]` が selected witness support rows から生成され、
  missing witness / unmeasured axis は zero curvature ではなく blocker として残る。
  `curvatureSupportReadings[]`、`curvatureTransferReadings[]`、transfer edges、
  `ArchitectureSpectrumReport` は Part IV distance refs を保持する。
- Lean 側に minimal theorem guardrail が追加され、`lake build` が通る。
- `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` が Lean 追加分と claim boundary を反映する。
- AAT 数学本文が ACTS の位置づけを、実装状況ではなく理論的 reading として反映する。
- `docs/tool/README.md`、`docs/tool/law_policy.md`、`docs/tool/archsig_analysis_packet.md` が ACTS report を説明する。
- public website / manual に出す場合は、spectrum report の読み方と non-conclusions が同期される。
- `cargo test --manifest-path tools/archsig/Cargo.toml` が通る。
- Lean 変更を含む場合は `lake build` が通る。
- `git diff --check` と hidden / bidirectional Unicode scan が通る。
