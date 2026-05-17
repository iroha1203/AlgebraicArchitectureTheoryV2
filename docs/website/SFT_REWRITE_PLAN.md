# SFT Website Rewrite Plan

この文書は、`website/sft/**` を全面的に作り直すための作業計画である。
複数セッションにまたがって作業しても意図が失われないように、構成思想、
削除方針、route、各ページの責務、書く範囲、書かない範囲、検証手順をここに固定する。

## 結論

現行の SFT website は流用しない。
既存の `website/sft/part-*` 構成は、研究本文の内部分類をそのまま公開ページへ写しており、
SFT の大きな魅力である次の三点を弱く見せている。

1. 開発組織全体を `field` として記述できる。
2. ソフトウェア進化を計算可能な対象にできる。
3. 計算された future に対して field intervention / control を設計できる。

したがって、SFT website は既存ページを編集して改善するのではなく、いったん削除し、
新しい三部構成で一から書き直す。

## Source of Truth

本文の primary source は次を使う。

- `docs/sft/software_field_theory.md`
- `docs/sft/aat_interface.md`
- `docs/outreach/en/aat_sft_hashnode_mvp_v_0_1.md`
- `docs/tool/software_field_reconstruction_protocol.md`
- `docs/tool/sft_calibration_benchmark.md`
- `docs/tool/ai_proposal_governance.md`
- `docs/tool/signature_artifacts.md`
- `docs/aat/mathematical_theory.md`
- `docs/aat/lean_theorem_index.md`
- `docs/aat/proof_obligations.md`

`website/sft/**` は source of truth ではない。公開読書面である。
website 独自の theorem claim、calibrated prediction claim、tool capability claim は追加しない。

## Core Thesis

SFT website 全体は、次の一文を支える構成にする。

```text
SFT describes the development organization as a field,
makes software evolution a computable object,
and studies how interventions reshape reachable architectural futures.
```

公開本文では、最初から claim boundary を前面に出さない。
ただし、境界を隠さない。境界は、危険な問いを計算可能にするための装甲として、
各ページの末尾、status、formal core、positioning に置く。

## 既存ページの扱い

まず現行 SFT ページを削除する。
削除対象は、少なくとも次を含む。

```text
website/sft/index.html
website/sft/part-i-new-object/
website/sft/part-ii-basis/
website/sft/part-iii-core/
website/sft/part-iv-principles/
website/sft/part-v-computing-systems/
website/sft/part-vi-case-studies/
website/sft/part-vii-research-program/
website/sft/theorem-candidates/
website/sft/status/
website/sft/glossary/
```

注意:

- 既存 HTML を機械的に移植しない。
- 使う場合も、文単位ではなく source docs へ戻って再構成する。
- `Coupon PRD` を canonical worked example として固定しない。
- 旧 `part-*` route は canonical sitemap から外す。
- 削除時に、他ページから旧 route へのリンクを残さない。

## 新しい全体構成

SFT は三部構成にする。

```text
/sft/
  Overview

1. The Development Organization as a Field
  /sft/field/
  /sft/field/codebase-memory/
  /sft/field/artifacts/
  /sft/field/agents/
  /sft/field/organization-structure/
  /sft/field/governance-feedback/
  /sft/field/architecture-futures/

2. Making Software Evolution Computable
  /sft/computation/
  /sft/computation/computable-slice/
  /sft/computation/aat-interface/
  /sft/computation/observation/
  /sft/computation/operation-support/
  /sft/computation/step-relation/
  /sft/computation/forecast-cone/
  /sft/computation/consequence-envelope/
  /sft/computation/support-safety/
  /sft/computation/proposal-accounting/
  /sft/computation/computational-problems/
  /sft/computation/archsig-pipeline/
  /sft/computation/simulator-calibration/

3. Field Intervention and Control
  /sft/intervention/
  /sft/intervention/governance/
  /sft/intervention/attractor-engineering/
  /sft/intervention/stable-regions/
  /sft/intervention/ai-governance/
  /sft/intervention/lifecycle/
  /sft/intervention/closed-loop/

References
  /sft/formal-core/
  /sft/theorem-candidates/
  /sft/research-program/
  /sft/positioning/
  /sft/status/
  /sft/glossary/
```

`docs/website/SITEMAP.md` が canonical route 管理である。
この計画書と `SITEMAP.md` が食い違う場合は、まず両者を同期する。

## Writing Rules

### Tone

- SFT を小さな review / CI 改善論にしない。
- SFT を「将来予測ツール」として売らない。
- SFT を比喩だけの socio-technical essay にしない。
- まず発見を見せ、その後で計算可能にするための境界を出す。
- `does not claim` から章を始めない。
- ただし、各ページ末尾では non-conclusion と claim boundary への導線を置く。

### Examples

- 固定の Coupon PRD を主役にしない。
- 具体例は、field dynamics を理解させるための短い挿入に留める。
- 具体例を出す場合は、「レビューで防げた事故」ではなく、
  「どの future が自然になったか」「何が観測可能になったか」を説明する。

### Page Size

目安:

- Overview: 短くする。abstract と chapter index が中心。
- Part landing page: 1,000-1,800 words 程度。
- Subpage: 1,200-2,500 words 程度。
- Reference page: 必要に応じて長くてよい。

## Page Specifications

### `/sft/` Overview

目的:

- SFT section の入口。
- 短い abstract と章インデックスだけを置く。

書くこと:

- SFT の一文定義。
- 三部構成の一覧。
- references への導線。

書かないこと:

- 長い manifesto。
- 詳細な claim level 表。
- theorem boundary の詳細。
- 具体 case study。

主な source:

- `docs/sft/software_field_theory.md` 冒頭。
- `docs/outreach/en/aat_sft_hashnode_mvp_v_0_1.md` の SFT 概要。

### `/sft/field/` 1. The Development Organization as a Field

目的:

- 第1部の入口。
- SFT の第一の強み「開発組織全体を記述できる」を立てる。

書くこと:

- SFT は codebase 単体ではなく development organization を field として読む。
- field は codebase、artifact、practice、agent、governance、feedback、lifecycle pressure からなる。
- field は未来を一意に決めないが、どの future が自然に見えるかを変える。

書かないこと:

- ここで `ForecastCone` の formal definition へ進まない。
- AAT theorem boundary の詳細へ入らない。

### `/sft/field/codebase-memory/` 1-1. Codebase as Field Memory

書くこと:

- codebase は implementation state だけではない。
- requirement、design decision、review history、CI history、incident、workaround、
  ownership boundary、tooling practice、latent default path が沈着した field memory である。
- 同じ module graph でも field memory が違えば次の自然な operation は変わる。

書かないこと:

- 静的 metric の話に落とさない。
- codebase memory から causal prediction が従うとは書かない。

主な source:

- `docs/sft/software_field_theory.md` Part I section 2。

### `/sft/field/artifacts/` 1-2. Artifacts Shape the Field

書くこと:

- PRD、spec、issue、design note、review comment、incident report を artifact-mediated force として読む。
- artifact は次の PR を決定しない。
- artifact は operation support、selection policy、observation boundary を変える。

書かないこと:

- PRD-to-PR predictor のように書かない。
- Coupon PRD を canonical example にしない。

主な source:

- `docs/sft/software_field_theory.md` sections 9, 21。
- `docs/outreach/en/aat_sft_hashnode_mvp_v_0_1.md` の PRD / force 説明。

### `/sft/field/agents/` 1-3. Developers and AI Agents

書くこと:

- developer と AI agent を field participant として扱う。
- AI agent は code proposal generator であるだけでなく local pattern amplifier である。
- codebase は AI agent にとって prompt でもある。

書かないこと:

- general AI safety を扱うページにしない。
- AI model quality 評価に縮めない。

主な source:

- `docs/sft/software_field_theory.md` sections 22, 28。
- `docs/tool/ai_proposal_governance.md`。

### `/sft/field/organization-structure/` 1-4. Organization Structure as Field

書くこと:

- Conway's Law を SFT の語彙で読む。
- communication path、ownership boundary、review route、approval flow、on-call boundary、
  issue decomposition が recurrent PR shape を作る。
- recurrent PR shape が architecture future を形作る。

書かないこと:

- Conway's Law を単なる metaphor にしない。
- 組織形態から architecture を deterministic に予測できるとは書かない。

主な source:

- `docs/outreach/en/aat_sft_hashnode_mvp_v_0_1.md` の Conway's Law section。

### `/sft/field/governance-feedback/` 1-5. Governance and Feedback

書くこと:

- review、CI、type checker、runtime observation、incident、postmortem、
  lifecycle pressure は field memory を更新する。
- governance は gate であるだけでなく future support を変える。

書かないこと:

- 詳細な intervention design は第3部へ送る。

主な source:

- `docs/sft/software_field_theory.md` sections 13, 14, 23。

### `/sft/field/architecture-futures/` 1-6. Architecture Futures

書くこと:

- SFT が見る future は確定未来ではなく reachable architectural futures。
- endpoint ではなく trajectory、signature movement、obstruction candidate、default path を見る。
- safe endpoint does not imply safe trajectory。

書かないこと:

- ForecastCone の formal definition は第2部へ送る。

主な source:

- `docs/sft/software_field_theory.md` section 4。
- 現行 `website/sft/part-i-new-object/` の counterexample anchor は必要に応じて参照する。

### `/sft/computation/` 2. Making Software Evolution Computable

目的:

- 第2部の入口。
- SFT の第二の強み「ソフトウェア進化を計算可能な対象にする」を立てる。

書くこと:

- computable とは deterministic prediction ではない。
- modeling boundary、observation axes、operation support、policy、horizon により bounded problem へ落とすこと。
- 第2部全体の地図。

書かないこと:

- 各 formal object の詳細を詰め込みすぎない。

### `/sft/computation/computable-slice/` 2-1. Computable Slice

書くこと:

- DevelopmentField 全体は大きすぎる。
- modeling boundary の下で SoftwareFieldEstimate を構成する。
- SoftwareField と architecture projection を定める。

書かないこと:

- complete reconstruction を主張しない。

主な source:

- `docs/sft/software_field_theory.md` sections 3, 8。
- `docs/tool/software_field_reconstruction_protocol.md`。

### `/sft/computation/aat-interface/` 2-2. AAT / SFT Interface

書くこと:

- AAT は SFT に依存しない。
- SFT は AAT の local algebra を architecture projection、observable coordinate、
  local transition law、admissibility premise として使う。
- AAT theorem は SFT forecast theorem ではない。

書かないこと:

- AAT の数学本文を再説明しすぎない。

主な source:

- `docs/sft/aat_interface.md`。

### `/sft/computation/observation/` 2-3. Observation Layer

書くこと:

- ArchSig は AAT でも SFT でもない。
- real artifact を AAT observables と SFT field estimate へ写す tooling layer。
- signature、obstruction、theorem boundary、unknown remainder を観測可能にする。

書かないこと:

- ArchSig の command manual にしない。

主な source:

- `docs/sft/aat_interface.md` section 6。
- `docs/tool/signature_artifacts.md`。
- `website/archsig/**` は surface 確認用。

### `/sft/computation/operation-support/` 2-4. Operation Support and Policy

書くこと:

- SFT の核心は、何が正しい変更かだけでなく、
  何が自然、低コスト、選ばれやすい変更として現れるかを見ること。
- OperationSupport、OperationPolicy、cost、selection。

書かないこと:

- 単なる prioritization / project management にしない。

主な source:

- `docs/sft/software_field_theory.md` section 10。

### `/sft/computation/step-relation/` 2-5. StepRelation and Field Paths

書くこと:

- supported operation による field transition。
- bounded path。
- future を path として扱う理由。

書かないこと:

- Lean 証明詳細は formal-core へ送る。

### `/sft/computation/forecast-cone/` 2-6. ForecastCone

書くこと:

- 未来の一点予測ではなく reachable future の cone。
- `ForecastCone(F, U, h)` の直感と bounded semantics。
- artifact action 後の cone family。

書かないこと:

- forecast correctness、probability weighting、causal proof を主張しない。

主な source:

- `docs/sft/software_field_theory.md` section 12。

### `/sft/computation/consequence-envelope/` 2-7. ConsequenceEnvelope

書くこと:

- ForecastCone は理論対象。
- ConsequenceEnvelope は reviewer / developer が読める report projection。
- path classes、affected axes、obstruction candidates、missing invariants、
  governance questions、unknown remainder。

書かないこと:

- Cone family から envelope が逆復元できるとは書かない。

主な source:

- `docs/sft/software_field_theory.md` section 12。

### `/sft/computation/support-safety/` 2-8. Support Safety and Cone Narrowing

書くこと:

- support inclusion、step simulation、safe region。
- selected boundary の下で cone projection / narrowing を扱う。
- global risk reduction とは区別する。

主な source:

- `docs/sft/software_field_theory.md` sections 15, 16。

### `/sft/computation/proposal-accounting/` 2-9. Proposal Accounting and Review Mediation

書くこと:

- raw proposal pressure、accepted proposal、rejected proposal、review-mediated transition を分ける。
- accepted change と future support preservation は別。
- review は単なる品質チェックではなく field process の一部。

主な source:

- `docs/sft/software_field_theory.md` section 17。

### `/sft/computation/computational-problems/` 2-10. SFT Computational Problems

書くこと:

- Field Reconstruction。
- Operation Support Inference。
- ConsequenceEnvelope Generation。
- Cone Narrowing。
- Support Safety Checking。
- Feedback Update。
- AI Proposal Governance。
- Lifecycle Decision。

書かないこと:

- 実装済み tool と未実装 research problem を混同しない。

主な source:

- `docs/sft/software_field_theory.md` section 20。

### `/sft/computation/archsig-pipeline/` 2-11. ArchSig-SFT Pipeline

書くこと:

- Markdown PRD / Spec / Issue / AI Proposal から
  ArtifactDescriptor、OperationSupportEstimate、ForecastConeSkeleton、
  ConsequenceEnvelope、ForecastCalibrationHook へ進む tooling surface。
- formal core との claim boundary。

書かないこと:

- ArchSig output から SFT forecast theorem が得られるとは書かない。

主な source:

- `docs/tool/reports.md`
- `docs/tool/signature_artifacts.md`
- `docs/sft/aat_interface.md` section 6。

### `/sft/computation/simulator-calibration/` 2-12. Simulator and Calibration

書くこと:

- PRD-to-ConsequenceEnvelope simulator は SFT を計算可能にする実現形。
- maturity level 0-6。
- forecast item refs と observed PR / review / CI / incident outcome refs の照合。
- calibration がない段階の envelope は bounded review artifact。

主な source:

- `docs/sft/software_field_theory.md` section 21。
- `docs/tool/sft_calibration_benchmark.md`。

### `/sft/intervention/` 3. Field Intervention and Control

目的:

- 第3部の入口。
- 計算された future に対して、field intervention をどう設計するかを扱う。

書くこと:

- intervention は単に悪い変更を止めることではない。
- support、policy、observation、feedback を変える。
- Attractor Engineering はこの章の代表的応用。

### `/sft/intervention/governance/` 3-1. Governance as Field Shaping

書くこと:

- review、CI、type checker、architecture rule、runtime guard、AI policy は quality gate ではなく governance intervention system。
- lawful path を低コスト化し、missing invariant を見つけ、field memory へ反映する。

主な source:

- `docs/sft/software_field_theory.md` section 23。

### `/sft/intervention/attractor-engineering/` 3-2. Attractor Engineering

書くこと:

- Attractor Engineering は SFT の代表的応用。
- 良い future が自然に選ばれ、悪い shortcut が高コスト・観測可能・review-mediated になるよう field を設計する。
- attractor / basin 語彙は魅力的に使うが、追加 semantics なしに強い theorem claim へ上げない。

書かないこと:

- SFT 全体を Attractor Engineering と同一視しない。

主な source:

- `docs/sft/software_field_theory.md` section 11。
- `docs/outreach/en/aat_sft_hashnode_mvp_v_0_1.md` の Attractor Engineering section。

### `/sft/intervention/stable-regions/` 3-3. Stable Regions and Recurrent Paths

書くこと:

- DefaultPath、RecurrentPattern、StableRegion、ReachablePreimage。
- attractor / basin に必要な追加 semantics。

主な source:

- `docs/sft/software_field_theory.md` section 19。

### `/sft/intervention/ai-governance/` 3-4. AI Proposal Governance

書くこと:

- AI proposal stream を bounded field model、prompt / policy boundary、
  theorem boundary、review / CI feedback の中で制御する。
- shortcut witness、hidden assumption、review load shift。

書かないこと:

- general AI safety を証明するページにしない。

主な source:

- `docs/sft/software_field_theory.md` section 22。
- `docs/tool/ai_proposal_governance.md`。

### `/sft/intervention/lifecycle/` 3-5. Lifecycle Decisions

書くこと:

- repair、migration、contraction、deletion、end-of-life。
- field capacity、runtime risk、ownership / staffing boundary、
  ConsequenceEnvelope family による bounded decision model。

主な source:

- `docs/sft/software_field_theory.md` section 24。

### `/sft/intervention/closed-loop/` 3-6. Closed-Loop Field Update

書くこと:

- forecast、actual PR、review、CI、incident outcome を照合する。
- posterior field update。
- calibration と feedback boundary update。

主な source:

- `docs/sft/software_field_theory.md` sections 14, 18。

### `/sft/formal-core/`

目的:

- 本編で出した直感のうち、どこが theorem-bearing fragment になるかを示す。

書くこと:

- SoftwareField。
- OperationSupport。
- StepRelation。
- ForecastCone。
- cone projection。
- support safety。
- FieldUpdate。
- EnvelopeProjection。
- AAT / ArchSig boundary。

書かないこと:

- empirical forecast correctness を Lean theorem のように書かない。

### `/sft/theorem-candidates/`

書くこと:

- theorem-shaped statements。
- counterexample anchors。
- Lean status。
- formalization targets。

主な source:

- existing `website/sft/theorem-candidates/` を参照してよいが、旧 navigation は捨てる。
- `docs/aat/lean_theorem_index.md`
- `docs/aat/proof_obligations.md`

### `/sft/research-program/`

書くこと:

- SFT Workbench。
- calibration。
- AI governance benchmark。
- lifecycle benchmark。
- closed-loop tooling。

書かないこと:

- 単なる未解決問題一覧にしない。
- stage / research ladder として読ませる。

### `/sft/positioning/`

書くこと:

- SFT は static metric、process model、DevOps maturity model、socio-technical metaphor、
  technical debt taxonomy、AI benchmark、formal verification そのものではない。
- SFT がそれらとどう違うか。

主な source:

- `docs/sft/software_field_theory.md` sections 30, 31。

### `/sft/status/`

書くこと:

- status vocabulary。
- claim levels。
- ForecastCone / ConsequenceEnvelope non-conclusions。
- ArchSig-SFT tooling boundary。
- Lean status。
- promotion rules。

書かないこと:

- top-level reading experience を status で重くしない。

### `/sft/glossary/`

書くこと:

- field。
- force。
- dissipation。
- attractor。
- basin。
- ForecastCone。
- ConsequenceEnvelope。
- support。
- policy。
- calibration。
- AAT / ArchSig / SFT の分担。

## Link and Redirect Strategy

旧 route を残すか redirect するかは実装時に決める。
no-build static site なので、必要なら旧 directory に minimal redirect HTML を置く。
ただし canonical sitemap には旧 `part-*` route を載せない。

候補:

```text
/sft/part-i-new-object/              -> /sft/field/
/sft/part-ii-basis/                  -> /sft/computation/aat-interface/
/sft/part-iii-core/                  -> /sft/computation/
/sft/part-iv-principles/             -> /sft/computation/support-safety/
/sft/part-v-computing-systems/       -> /sft/computation/computational-problems/
/sft/part-vi-case-studies/           -> /sft/intervention/
/sft/part-vii-research-program/      -> /sft/research-program/
```

## Implementation Order

1. `docs/website/SITEMAP.md` とこの計画書を同期する。
2. `docs/website/DESIGN.md` の SFT 旧 Part 構成を更新する。
3. `website/sft/**` を削除または退避せず削除する。
4. 共通 page template を決める。
5. `/sft/` overview を作る。
6. 第1部を作る。
7. 第2部を作る。
8. 第3部を作る。
9. reference pages を作る。
10. `website/sitemap.xml` を更新する。
11. `website/llms.txt` に必要な canonical SFT routes を反映する。
12. site-wide navigation と sidebar links を新 route へ更新する。
13. static verification を行う。

## Verification

website 変更後は次を確認する。

- `git diff --check`
- hidden / bidirectional Unicode scan
- `website/sitemap.xml` と `docs/website/SITEMAP.md` の route 一致
- 旧 `part-*` links が残っていないこと
- root-absolute asset path がないこと
- no-build static page として local preview できること
- Playwright で主要 pages の title、links、layout を確認すること

Codex から Playwright を実行する場合は、sandbox 外実行が必要になることがある。
`AGENTS.md` の website policy に従う。

## Open Decisions

まだ決めていない事項:

- 旧 route を redirect HTML として残すか、完全削除するか。
- `website/sft/status/` と `website/sft/theorem-candidates/` は既存内容をどこまで再利用するか。
- 各 page に commit-pinned source links をどの release snapshot で置くか。
- figure / diagram の共通 component を新しく作るか、既存 CSS class に寄せるか。

この文書の意図に反しない限り、実装セッションでは小さな編集判断を進めてよい。
ただし、三部構成、既存 SFT ページを一から書き直す方針、canonical route から旧 Part
構成を外す方針は変更しない。
