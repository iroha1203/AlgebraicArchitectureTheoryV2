# Website Design

この文書は、AAT / SFT 公開サイトの設計方針、読者導線、ページネーション、
本文成熟度、source mapping を管理する。

route と production `sitemap.xml` の対応は [SITEMAP.md](SITEMAP.md) に置く。

## 基本方針

- `website/` は no-build の静的サイトとして運用する。
- URL は directory route に統一し、各ページは `index.html` を持つ。
- 公開サイトの source of truth は英語とし、prefix なしの route に置く。
- 日本語は Qiita、Zenn、Hashnode などの outreach article として扱い、site mirror は作らない。
- `docs/` は source of truth、`website/` は public reading surface として扱う。
- 数学本文、Lean status、proof obligation、tooling claim、empirical hypothesis を混同しない。
- AAT の数学的 source of truth は `docs/aat/mathematical_theory.md` とする。
  `website/aat/**` はこれを置き換える正典ではなく、同文書に忠実な publication
  edition / web-native monograph として肉付けする。
- AAT は first-class formal theory article として、`docs/aat/mathematical_theory.md`
  に忠実な論文調の本文を章クラスタ単位で見せる。
- AAT website は、Gauss の `Disquisitiones Arithmeticae` が整数論を体系化した
  ように、AAT を定義、命題、証明アイデア、例、反例、Lean status の順に読める
  体系本文として編成する。ただし、website 独自の theorem claim は置かず、理論上の
  新規 claim は先に `docs/aat/mathematical_theory.md` へ反映する。
- AAT website は web-native preprint / monograph として扱う。Hashnode、Zenn、
  Qiita のような outreach surface では維持しにくい定義、前提、theorem boundary、
  反例、Lean status、non-conclusions を一箇所で読めるようにする。
- AAT の公開 theory pages は release snapshot を表示し、参照元 docs への GitHub
  links は公開時点の commit に固定する。`blob/main` は作業中の便宜には使えても、
  paper-grade public reference の citation としては使わない。
- SFT は first-class research monograph として、`docs/sft/software_field_theory.md`
  に忠実な論文調の本文を Part 単位で見せる。
- AAT / SFT page は marketing summary や一般向け article ではなく、定義、前提、
  theorem boundary、non-conclusions、例、Lean status への接続を持つ技術本文として書く。
- ArchSig は standalone manual / reference section として扱う。
- Hashnode / Zenn / Qiita は outreach 導線であり、canonical claim の置き場にしない。

## トップレベル route 設計

英語版が canonical route である。
日本語はこの site の mirror route ではなく、outreach article への導線として扱う。

```text
/
  トップページ。
  著者プロフィールの短い導入、AAT / SFT / ArchSig の入口、主要 article への導線。

/profile/
  著者プロフィール、連絡先、GitHub、公開活動。

/aat/
  AAT landing。
  AAT の位置づけ、読む順序、章クラスタ、status / repository docs への入口。

/aat/foundations/
  AAT Part I. Foundations。
  中心命題、ArchitectureObject、ArchitectureCore、ComponentUniverse。

/aat/laws-and-witnesses/
  AAT Part II. Laws and Witnesses。
  Invariant、LawUniverse、ObstructionWitness、零曲率。

/aat/architecture-signature/
  AAT Part III. Architecture Signature。
  ArchitectureSignature、TheoremBoundary、Non-conclusions。

/aat/local-law-packages/
  AAT Part IV. Local Law Packages。
  Projection、Observation、LSP、DIP、Three-layer Flatness。

/aat/calculus-and-extensions/
  AAT Part V. Calculus and Extensions。
  ArchitectureCalculus、FeatureExtension、ExtensionObstruction。

/aat/repair-and-dynamics/
  AAT Part VI. Repair and Dynamics。
  Repair、Synthesis、ComplexityTransfer、Path、Homotopy、DiagramFilling。

/aat/representations-and-effects/
  AAT Part VII. Representations and Effects。
  Graph、Matrix、AnalyticRepresentation、StateTransitionAlgebra、EffectBoundary。

/aat/examples-and-boundaries/
  AAT Part VIII. Examples and Boundaries。
  Canonical examples、counterexamples、AAT の境界。

/aat/related-work/
  AAT appendix. Related Work and Novelty。
  ISO 42010、ATAM、architecture metrics、graph analysis、formal methods、
  category-theoretic models との関係と novelty boundary。

/aat/status/
  AAT Lean status。
  Lean theorem index、proof obligations、proved / defined only / future obligation の読み方。

/interface/
  AAT -> SFT interface。
  片方向依存、claim translation、禁止される読み替え。

/sft/
  SFT landing。
  SFT の短い abstract、三部構成、reference pages への入口。

/sft/field-and-force/
  1. Field and Force。
  codebase memory and artifact force、agents and organization、
  governance feedback and architecture futures への入口。

/sft/computation/
  2. Making Software Evolution Computable。
  computable slice、AAT interface、observation、operation support、step relation、
  ForecastCone、ConsequenceEnvelope、support safety、proposal accounting、
  computational problems、ArchSig pipeline、calibration への入口。

/sft/software-evolution/
  3. Software Evolution。
  governance and attractor engineering、AI proposal governance、
  lifecycle and closed-loop evolution への入口。

/sft/formal-core/
  Formal Core。
  theorem-bearing fragment、empirical / tooling claim boundary、AAT / ArchSig boundary。

/sft/theorem-candidates/
  Theorem Candidates。
  theorem-shaped statements、counterexample anchors、Lean status、formalization targets。

/sft/research-program/
  Research Program。
  workbench、calibration、AI governance benchmark、lifecycle benchmark、
  closed-loop tooling を research ladder として整理する。

/sft/positioning/
  Positioning and Non-Conclusions。
  static metric、process model、DevOps maturity model、metaphor、AI benchmark、
  formal verification との非混同。

/sft/status/
  Status and Claim Boundaries。
  claim levels、non-conclusions、promotion rules、Lean / empirical / tooling boundary。

/sft/glossary/
  Glossary。
  field、force、attractor、basin、ForecastCone、ConsequenceEnvelope、support、policy、
  calibration の用語境界。

/archsig/
  ArchSig manual landing。
  できること、できないこと、読む順序、Core / Review / SFT / Operational surface、
  CLI / artifact / workflow / reference への入口。

/archsig/getting-started/
  最短手順。
  fixture scan、validate、repository scan、Python repository scan。advanced surface は
  command / artifact / workflow page に分ける。

/archsig/commands/
  Command reference。
  scan、validate、snapshot、signature-diff、air、theorem-check、feature-report、
  policy-decision、pr-comment、registry / schema / SFT forecasting commands。

/archsig/artifacts/
  Artifact reference。
  Sig0、validation report、snapshot、diff report、AIR、Feature Extension Report、
  policy decision、PR comment、dataset、operational feedback、SFT forecasting artifacts。

/archsig/boundaries/
  Reading rules and boundaries。
  measurement boundary、claim boundary、non-conclusions、formal claim promotion guardrails。

/archsig/workflows/
  Workflow manual。
  first adoption、PR review、generated-change provenance、scheduled scan、
  architecture dynamics workflow、SFT forecasting workflow。

/archsig/schemas/
  Schema and compatibility reference。
  schema version policy、compatibility outcomes、catalog、migration rules。

/archsig/operational-feedback/
  Operational feedback manual。
  B10 daily ledger、calibration review、team threshold policy、ownership boundary monitor、
  repair adoption、incident correlation、hypothesis refresh。

/archsig/examples/
  Examples and report reading。
  good extension、hidden interaction witness、semantic witness、Feature Extension Report reading。

/archsig/roadmap/
  Tooling roadmap。
  B0-B13 phases、standardization targets、remaining gaps、future ArchSig / SFT forecasting work。

/outreach/
  Hashnode, Zenn, Qiita, talks, short articles。
  各 outreach article から canonical technical article へ戻る導線を置く。
```

## 言語と outreach ルール

- 公開サイトの source of truth は英語とする。
- `/ja/` mirror route は作らない。
- 実際の日本語 site strategy が決まるまで language switch は追加しない。
- 日本語の説明は Qiita、Zenn、Hashnode などの outreach article として扱う。
- outreach article は、形式的主張に関して canonical English page へ戻る導線を持つ。
- outreach article は動機や直観を簡略化してよいが、AAT / SFT website pages は
  paper-level precision を保ち、読みやすさのために assumption や theorem boundary
  を省略しない。
- AAT / SFT terminology は過度に翻訳しない。`ArchitectureObject`, `Invariant`,
  `ObstructionWitness`, `ArchitectureSignature`, `ForecastCone`,
  `ConsequenceEnvelope` などの core terms は、曖昧さを避けるため必要に応じて英語のまま残す。
- 日本語 article は動機と直観を説明してよいが、theorem status、claim boundary、
  canonical definition は英語サイトと repository docs 側に残す。

## グローバルナビゲーション

グローバル nav は最初から増やしすぎない。

```text
Home
AAT
Interface
SFT
ArchSig
Outreach
Profile
```

`AAT` と `SFT` は landing に向ける。
長い本文や Part ページは、landing から secondary navigation で辿る。
`ArchSig` は `/archsig/` に向ける。

## 読書導線

### 初見読者向け

```text
/ -> /aat/ -> /sft/ -> /outreach/
```

目的は、研究の全体像を短時間で掴ませること。
厳密な定義や証明状態へ無理に誘導しない。

### 技術読者向け

```text
/ -> /aat/ -> /aat/foundations/ -> ... -> /aat/status/ -> /interface/ -> /sft/
```

目的は、AAT の formal core と claim boundary を読んでから SFT へ入ること。

### AAT 読者向け

```text
/aat/
  -> /aat/foundations/
  -> /aat/laws-and-witnesses/
  -> /aat/architecture-signature/
  -> /aat/local-law-packages/
  -> /aat/calculus-and-extensions/
  -> /aat/repair-and-dynamics/
  -> /aat/representations-and-effects/
  -> /aat/examples-and-boundaries/
  -> /aat/related-work/
  -> /aat/status/
```

AAT は Web では一枚にしない。
`docs/aat/mathematical_theory.md` は単一の第一級本文として維持しつつ、
公開サイトでは章クラスタ単位に分ける。

### SFT 読者向け

```text
/sft/
  -> /sft/field-and-force/
  -> /sft/computation/
  -> /sft/software-evolution/
  -> /sft/formal-core/
  -> /sft/theorem-candidates/
  -> /sft/research-program/
  -> /sft/positioning/
  -> /sft/status/
  -> /sft/glossary/
```

SFT は三部構成で読み、reference pages で theorem boundary、status、glossary、
positioning、research ladder を本編から分離して読む。

### ArchSig / 実装読者向け

```text
/ -> /archsig/ -> /archsig/getting-started/ -> /archsig/commands/ -> /archsig/artifacts/
```

目的は、ArchSig を実際に動かし、artifact を読み、claim boundary を誤読しないこと。

### ArchSig reference 読者向け

```text
/archsig/
  -> /archsig/getting-started/
  -> /archsig/commands/
  -> /archsig/artifacts/
  -> /archsig/boundaries/
  -> /archsig/workflows/
  -> /archsig/schemas/
  -> /archsig/operational-feedback/
  -> /archsig/examples/
  -> /archsig/roadmap/
```

ArchSig は発展中だが、すでに CLI、schema、artifact、report、workflow の規模を持つ。
したがって、単なる research note ではなく、manual / reference として読める構成にする。

## ページネーション規則

### AAT

AAT article は章クラスタ単位でページ分割する。
`docs/aat/mathematical_theory.md` は 16 章の単一 source of truth として維持し、
公開サイトでは読者の現在地が見える粒度に分割する。

分割は原則として 2 章前後を 1 ページにまとめる。
ただし、`ArchitectureSignature` と `TheoremBoundary` のように claim discipline 上で
一緒に読ませたい章は同じページに置く。

```text
/aat/
  next: /aat/foundations/

/aat/foundations/
  previous: /aat/
  next:     /aat/laws-and-witnesses/

/aat/laws-and-witnesses/
  previous: /aat/foundations/
  next:     /aat/architecture-signature/

/aat/architecture-signature/
  previous: /aat/laws-and-witnesses/
  next:     /aat/local-law-packages/

/aat/local-law-packages/
  previous: /aat/architecture-signature/
  next:     /aat/calculus-and-extensions/

/aat/calculus-and-extensions/
  previous: /aat/local-law-packages/
  next:     /aat/repair-and-dynamics/

/aat/repair-and-dynamics/
  previous: /aat/calculus-and-extensions/
  next:     /aat/representations-and-effects/

/aat/representations-and-effects/
  previous: /aat/repair-and-dynamics/
  next:     /aat/examples-and-boundaries/

/aat/examples-and-boundaries/
  previous: /aat/representations-and-effects/
  next:     /aat/related-work/

/aat/related-work/
  previous: /aat/examples-and-boundaries/
  next:     /aat/status/

/aat/status/
  previous: /aat/related-work/
  next:     /interface/
```

`/aat/status/` は appendix 的に扱い、AAT 本文からは明確に分離する。

### Interface

Interface は AAT と SFT の橋なので、前後導線を固定する。

```text
/interface/
  previous: /aat/status/
  next:     /sft/
```

### SFT

SFT は三部構成と reference pages に分けてページネーションする。

```text
/sft/
  next: /sft/field-and-force/

/sft/field-and-force/
  previous: /sft/
  next:     /sft/computation/

/sft/computation/
  previous: /sft/field-and-force/
  next:     /sft/software-evolution/

/sft/software-evolution/
  previous: /sft/computation/
  next:     /sft/formal-core/

/sft/formal-core/
  previous: /sft/software-evolution/lifecycle-closed-loop/
  next:     /sft/theorem-candidates/

/sft/theorem-candidates/
  previous: /sft/formal-core/
  next:     /sft/research-program/

/sft/research-program/
  previous: /sft/theorem-candidates/
  next:     /sft/positioning/

/sft/positioning/
  previous: /sft/research-program/
  next:     /sft/status/

/sft/status/
  previous: /sft/positioning/
  next:     /sft/glossary/

/sft/glossary/
  previous: /sft/status/
  next:     /archsig/
```

SFT の三部構成には下位 route を置く。reference pages は本編の claim boundary と用語境界を
支える appendix として扱い、三部構成の本文そのものを置き換えない。

### ArchSig

ArchSig は manual / reference section としてページネーションする。

```text
/archsig/
  previous: /sft/glossary/
  next:     /archsig/getting-started/

/archsig/getting-started/
  previous: /archsig/
  next:     /archsig/commands/

/archsig/commands/
  previous: /archsig/getting-started/
  next:     /archsig/artifacts/

/archsig/artifacts/
  previous: /archsig/commands/
  next:     /archsig/boundaries/

/archsig/boundaries/
  previous: /archsig/artifacts/
  next:     /archsig/workflows/

/archsig/workflows/
  previous: /archsig/boundaries/
  next:     /archsig/schemas/

/archsig/schemas/
  previous: /archsig/workflows/
  next:     /archsig/operational-feedback/

/archsig/operational-feedback/
  previous: /archsig/schemas/
  next:     /archsig/examples/

/archsig/examples/
  previous: /archsig/operational-feedback/
  next:     /archsig/roadmap/

/archsig/roadmap/
  previous: /archsig/examples/
  next:     /outreach/
```

### Outreach と Profile

ArchSig manual 以降は hub page として扱う。

```text
/outreach/
  previous: /archsig/roadmap/
  next:     /profile/

/profile/
  previous: /outreach/
  next:     /
```

## ページテンプレート要件

各ページは次を持つ。

- global navigation
- page title
- short abstract / page role
- local table of contents, when the page is long
- canonical source link to `docs/` or GitHub
- previous / next navigation, when the page belongs to a reading sequence
- claim boundary note, when formal / tooling / empirical levels may be confused

## ArchSig page の参照元対応

ArchSig page は、`docs/tool/` と `tools/archsig/docs/` の両方を source として使う。

| Website page | Primary source documents | Role |
| --- | --- | --- |
| `/archsig/` | `tools/archsig/README.md`, `docs/tool/README.md`, `docs/tool/principles.md` | Manual landing and conceptual boundary. |
| `/archsig/getting-started/` | `tools/archsig/README.md` | Minimal Core command path for first run. |
| `/archsig/commands/` | `tools/archsig/docs/commands.md` | CLI command reference grouped by Core / Review / SFT / Operational surface. |
| `/archsig/artifacts/` | `tools/archsig/docs/artifacts-and-boundaries.md`, `docs/tool/signature_artifacts.md`, `docs/tool/reports.md`, `docs/tool/air.md` | Artifact and report reference grouped by product surface. |
| `/archsig/boundaries/` | `tools/archsig/docs/artifacts-and-boundaries.md`, `docs/tool/claim_boundary.md`, `docs/tool/theorem_preconditions.md` | Measurement / claim boundary reading rules. |
| `/archsig/workflows/` | `docs/tool/workflows.md`, `tools/archsig/README.md` | Adoption, PR review, scheduled scans, dynamics workflows. |
| `/archsig/schemas/` | `docs/tool/schema_compatibility.md`, `docs/tool/air.md`, `docs/tool/signature_artifacts.md` | Schema versioning and compatibility reference. |
| `/archsig/operational-feedback/` | `tools/archsig/docs/operational-feedback.md`, `docs/tool/reports.md` | B10 operational feedback artifacts and reading rules. |
| `/archsig/examples/` | `docs/tool/examples.md`, `docs/tool/repair_suggestion.md` | Report examples and repair suggestion reading. |
| `/archsig/roadmap/` | `docs/tool/roadmap.md` | Tooling roadmap, remaining gaps, and standardization targets. |

ArchSig reference pages must keep these warnings visible:

- `archsig` is not a Lean prover.
- tool output is not a Lean theorem.
- extractor output is not a complete `ComponentUniverse`.
- measured zero is different from unmeasured.
- policy pass does not imply architecture lawfulness.
- report warning does not imply incident causality.

## 現在の実装状態

`implemented` は route existence の状態だけを表す。
本文が canonical source に忠実か、論文調の exposition として十分か、Lean status /
claim boundary への導線を持つか、ArchSig manual として成熟しているかは別に管理する。

```text
implemented:
  /
  /aat/
  /aat/foundations/
  /aat/laws-and-witnesses/
  /aat/architecture-signature/
  /aat/local-law-packages/
  /aat/calculus-and-extensions/
  /aat/repair-and-dynamics/
  /aat/representations-and-effects/
  /aat/examples-and-boundaries/
  /aat/related-work/
  /aat/status/
  /interface/
  /sft/
  /sft/field-and-force/
  /sft/field-and-force/codebase-memory-artifact-force/
  /sft/field-and-force/agents-organization-recurrent-paths/
  /sft/field-and-force/governance-feedback-futures/
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
  /sft/software-evolution/
  /sft/software-evolution/governance-attractor-engineering/
  /sft/software-evolution/ai-proposal-governance/
  /sft/software-evolution/lifecycle-closed-loop/
  /sft/formal-core/
  /sft/theorem-candidates/
  /sft/research-program/
  /sft/positioning/
  /sft/status/
  /sft/glossary/
  /archsig/
  /archsig/getting-started/
  /archsig/commands/
  /archsig/artifacts/
  /archsig/boundaries/
  /archsig/workflows/
  /archsig/schemas/
  /archsig/operational-feedback/
  /archsig/examples/
  /archsig/roadmap/
  /outreach/
  /profile/
```

## 本文成熟度

Content maturity は route implementation とは独立に管理する。
AAT / SFT / ArchSig / Outreach / Profile は期待される成熟度が違うため、
同じ `implemented` route でも要求される本文量、source fidelity、claim boundary の厚さは異なる。

### 成熟度の軸

| Dimension | Meaning | Target reading |
| --- | --- | --- |
| Route existence | directory route と `index.html` が存在するか。 | `implemented` は navigation と publishing surface の存在だけを意味する。 |
| Canonical-source fidelity | `docs/` または tool docs の source of truth に忠実か。 | AAT は `docs/aat/mathematical_theory.md`、SFT は `docs/sft/software_field_theory.md`、ArchSig は `docs/tool/` と `tools/archsig/docs/` を source とする。 |
| Paper-level exposition | 定義、前提、例、non-conclusions、theorem / claim boundary を本文で展開しているか。 | AAT / SFT の章・Part pages では必須。Outreach / Profile では必須ではない。 |
| Lean / claim boundary links | Lean theorem status、proof obligations、empirical hypothesis、tool output を混同しない導線があるか。 | AAT は Lean status への接続、SFT は empirical / forecast status の境界、ArchSig は tool output と theorem claim の境界を明示する。 |
| Tool / manual maturity | ArchSig CLI、schema、artifact、workflow を利用者が実行・解釈できる manual として読めるか。 | ArchSig section だけの maturity dimension。AAT / SFT では `not applicable` とする。 |

### AAT publication edition の期待値

`website/aat/**` は `docs/aat/mathematical_theory.md` を正典として参照しつつ、
出版物としての体系本文を提供する。各章は、可能な限り次の型に沿って展開する。

```text
Definition
-> Lemma / Proposition / Theorem
-> Proof idea
-> Example
-> Counterexample / Non-conclusion
-> Lean status
```

この型の目的は、status table や境界台帳を本文の代替にしないことである。章本文では
定義から命題へ進む数学的な流れを主に置き、Lean status、proof obligation、
non-conclusion は各命題の近くで追跡可能にする。章末の status table は索引や一覧の
補助として使い、theorem-grade な主張そのものは本文中で、命題名、Lean 名、status、
仮定、境界、non-conclusion と対応させる。

website で追加してよい内容は、正典本文に基づく説明、proof idea、読者向け導入、
例の詳説、反例の解説、Lean status card、source mapping である。website だけに
新しい定義、定理候補、証明済み claim、non-conclusion の変更を置いてはならない。
そのような変更が必要な場合は、先に `docs/aat/mathematical_theory.md`、
`docs/aat/proof_obligations.md`、または `docs/aat/lean_theorem_index.md` の
対応箇所を更新する。

本文中の theorem-grade claim は、必要に応じて `theorem-card` / `lean-status-card` パターンで
命題名、Lean anchor、status、仮定、境界、non-conclusion を近接表示する。
章末 table は索引補助として残してよいが、`proved`、`defined only`、
`future proof obligation`、`empirical hypothesis` の格上げや混同を避ける。

### セクションごとの期待値

| Section | Route status | Expected maturity | Current maturity | Remaining work |
| --- | --- | --- | --- | --- |
| `/aat/` landing | implemented | AAT の読む順序、source docs、Lean status、related work への入口を明示する overview。 | route, overview, and related-work entry implemented。 | 子 chapter や status 更新に合わせて reading path と source links を維持する。 |
| `/aat/*/` chapter pages | implemented | `docs/aat/mathematical_theory.md` を正典とする publication edition。Definition -> Proposition/Theorem -> Proof idea -> Example -> Counterexample / Non-conclusion -> Lean status の型で、DA 的な体系本文として読める。 | #772 closed。chapter-cluster pages are implemented with definitions, examples, boundary notes, and Lean/status links where relevant。 | source commit pin、Lean status link、claim boundary wording を継続点検し、status table 中心の箇所を命題単位の本文と theorem card へ移行する。 |
| `/aat/related-work/` | implemented | adjacent work との関係と novelty boundary を示す appendix。 | related-work synthesis implemented。 | 参照領域が増えた場合に novelty boundary と non-replacement claim を更新する。 |
| `/aat/status/` | implemented | proved / defined only / future proof obligation を読むための status appendix。 | route and status overview implemented。 | AAT chapter / related-work からの参照と theorem index への導線を点検する。 |
| `/interface/` | implemented | AAT theorem claim と SFT empirical / computational claim の translation boundary。 | route and boundary overview implemented。 | AAT / SFT 本文増補後、禁止される読み替えと依存方向の記述を再点検する。 |
| `/sft/` landing | implemented | SFT の読む順序、三部構成、reference pages への入口。 | route and overview implemented with three-part index and references。 | 子 page の増補に合わせて computational reading と source docs への導線を維持する。 |
| `/sft/field-and-force/*`, `/sft/computation/*`, `/sft/software-evolution/*` pages | implemented | canonical SFT monograph に忠実な research exposition。 | 三部構成の page 群が definitions, computational readings, examples, claim boundaries, non-conclusions を持つ。 | W3 で AAT theorem status と SFT empirical / forecast status の境界導線を継続点検する。 |
| `/sft/formal-core/`, `/sft/theorem-candidates/`, `/sft/research-program/`, `/sft/positioning/`, `/sft/status/`, `/sft/glossary/` | implemented | SFT reference appendix。formal core、theorem candidates、research ladder、positioning、status vocabulary、glossary を本編から分離する。 | reference pages implemented。 | route 追加や claim boundary 更新時に sitemap、llms、status vocabulary を同期する。 |
| `/archsig/` and `/archsig/*/` | implemented | standalone manual / reference。tool output と formal claim を区別し、CLI、artifact、schema、workflow を読める。 | Core / Review / SFT / Operational surface と remaining gaps を整理済み。 | W3 で cross-link と boundary wording を継続点検する。 |
| `/outreach/` | implemented | canonical technical pages へ戻す outreach index。 | route implemented。 | article が増えた時点でリンクと canonical return path を更新する。 |
| `/profile/` | implemented | author profile and contact surface。 | route implemented。 | 研究成果・公開活動の変化に応じて更新する。 |

### phase 管理

```text
W2 first-class theory / manual surface:
  done:
    - route implementation for AAT, SFT, Interface, ArchSig, Outreach, Profile
    - content maturity tracking in this document
    - #772 AAT chapter pages: paper-level canonical exposition
    - #774 ArchSig / tool docs: product surface and remaining gaps
    - #773 SFT Part pages: monograph-level canonical exposition

W3 cross-link and boundary hardening:
  remaining:
    - verify AAT pages link to Lean status without treating all mathematical text as proved
    - verify SFT pages keep forecast / empirical claims separate from AAT theorem status
    - verify ArchSig pages keep tool evidence separate from formal theorem claims
    - add or update source links after W2 content expansion changes route-level references

W4 publication polish:
  remaining:
    - review long-form reading flow after W2 / W3 changes
    - keep `website/sitemap.xml` aligned with implemented routes under `https://iroha1203.dev/`
    - replace remaining `blob/main` source links with commit-pinned URLs where a release snapshot requires drift-free citation
    - update outreach return paths when external articles are published
```

## SEO sitemap 方針

公開ドメインは `iroha1203.dev`。

`website/sitemap.xml` は `https://iroha1203.dev/` を URL base として、実装済みの
canonical public routes を列挙する。

`website/robots.txt` は production sitemap を指す。
