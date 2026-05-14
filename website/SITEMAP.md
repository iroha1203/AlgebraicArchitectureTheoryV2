# Website Sitemap

この文書は、AAT / SFT 公開サイトの構成、URL、ページ遷移、ページネーションを固めるための設計図である。
SEO 用の `sitemap.xml` ではない。

## 基本方針

- `website/` は no-build の静的サイトとして始める。
- URL は directory route に統一し、各ページは `index.html` を持つ。
- 公開サイトの source of truth は英語とし、prefix なしの route に置く。
- 日本語は Qiita、Zenn、Hashnode などの outreach article として扱い、site mirror は作らない。
- `docs/` は source of truth、`website/` は public reading surface として扱う。
- 数学本文、Lean status、proof obligation、tooling claim、empirical hypothesis を混同しない。
- AAT は formal theory article を章クラスタ単位で分割して見せる。
- SFT は theory site / research monograph として Part 単位で見せる。
- ArchSig は standalone manual / reference section として扱う。
- Hashnode / Zenn / Qiita は outreach 導線であり、canonical claim の置き場にしない。

## Top-Level Map

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

/aat/signature-and-boundary/
  AAT Part III. Signature and Theorem Boundary。
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

/aat/status/
  AAT Lean status。
  Lean theorem index、proof obligations、proved / defined only / future obligation の読み方。

/interface/
  AAT -> SFT interface。
  片方向依存、claim translation、禁止される読み替え。

/sft/
  SFT landing。
  SFT の位置づけ、Part 一覧、computable core、claim boundary への入口。

/sft/part-i-new-object/
  Part I. The New Object。
  software evolution as computable object, codebase as field memory, development field。

/sft/part-ii-basis/
  Part II. Algebraic and Observational Basis。
  AAT dependency, ArchSig bridge, claim boundaries。

/sft/part-iii-core/
  Part III. SFT Core。
  SoftwareField, artifact-mediated change, operation support, policy, ForecastCone, FieldUpdate。

/sft/part-iv-principles/
  Part IV. Principles and Theorems。
  ForecastCone narrowing, support safety, proposal accounting, feedback boundary update。

/sft/part-v-computing-systems/
  Part V. Computing Systems Built from SFT。
  computational problems, PRD simulator, AI governance, review / CI, lifecycle。

/sft/part-vi-case-studies/
  Part VI. Case Studies。
  Coupon PRD, migration, incident response, AI-generated shortcut, end-of-life decision。

/sft/part-vii-research-program/
  Part VII. Non-Conclusions and Research Program。
  positioning, non-claims, open problems, workbench direction。

/archsig/
  ArchSig manual landing。
  できること、できないこと、読む順序、CLI / artifact / workflow / reference への入口。

/archsig/getting-started/
  最短手順。
  fixture scan、validate、repository scan、Python repository scan。

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
  B0-B13 phases、standardization targets、future ArchSig / SFT forecasting work。

/outreach/
  Hashnode, Zenn, Qiita, talks, short articles。
  各 outreach article から canonical technical article へ戻る導線を置く。
```

## Language And Outreach Rules

- Site source of truth: English.
- No `/ja/` mirror route.
- Do not add a language switch unless a real Japanese site strategy exists.
- Japanese explanations should live as outreach articles on Qiita, Zenn, Hashnode, or similar media.
- Outreach articles should point back to the canonical English page for formal claims.
- AAT / SFT terminology should not be translated aggressively. Keep core terms such as `ArchitectureObject`, `Invariant`, `ObstructionWitness`, `ArchitectureSignature`, `ForecastCone`, and `ConsequenceEnvelope` in English when that avoids ambiguity.
- Japanese articles may explain motivation and intuition, but theorem status, claim boundaries, and canonical definitions remain on the English site and repository docs.

## Global Navigation

グローバル nav は最初から増やしすぎない。

```text
Home
AAT
SFT
Interface
ArchSig
Outreach
Profile
```

`AAT` と `SFT` は landing に向ける。
長い本文や Part ページは、landing から secondary navigation で辿る。
`ArchSig` は `/archsig/` に向ける。

## Reading Paths

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
  -> /aat/signature-and-boundary/
  -> /aat/local-law-packages/
  -> /aat/calculus-and-extensions/
  -> /aat/repair-and-dynamics/
  -> /aat/representations-and-effects/
  -> /aat/examples-and-boundaries/
  -> /aat/status/
```

AAT は Web では一枚にしない。
`docs/aat/mathematical_theory.md` は単一の第一級本文として維持しつつ、
公開サイトでは章クラスタ単位に分ける。

### SFT 読者向け

```text
/sft/
  -> /sft/part-i-new-object/
  -> /sft/part-ii-basis/
  -> /sft/part-iii-core/
  -> /sft/part-iv-principles/
  -> /sft/part-v-computing-systems/
  -> /sft/part-vi-case-studies/
  -> /sft/part-vii-research-program/
```

SFT は長いので、Part 単位で明示的に分割する。
各 Part の中では、当面は章内 anchor と local table of contents で処理する。

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

ArchSig は未完成であっても、すでに CLI、schema、artifact、report、workflow の規模を持つ。
したがって、単なる research note ではなく、manual / reference として読める構成にする。

## Pagination Rules

### AAT

AAT article は v1 から章クラスタ単位でページ分割する。
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
  next:     /aat/signature-and-boundary/

/aat/signature-and-boundary/
  previous: /aat/laws-and-witnesses/
  next:     /aat/local-law-packages/

/aat/local-law-packages/
  previous: /aat/signature-and-boundary/
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
  next:     /aat/status/

/aat/status/
  previous: /aat/examples-and-boundaries/
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

SFT は Part 単位でページネーションする。

```text
/sft/
  next: /sft/part-i-new-object/

/sft/part-i-new-object/
  previous: /sft/
  next:     /sft/part-ii-basis/

/sft/part-ii-basis/
  previous: /sft/part-i-new-object/
  next:     /sft/part-iii-core/

/sft/part-iii-core/
  previous: /sft/part-ii-basis/
  next:     /sft/part-iv-principles/

/sft/part-iv-principles/
  previous: /sft/part-iii-core/
  next:     /sft/part-v-computing-systems/

/sft/part-v-computing-systems/
  previous: /sft/part-iv-principles/
  next:     /sft/part-vi-case-studies/

/sft/part-vi-case-studies/
  previous: /sft/part-v-computing-systems/
  next:     /sft/part-vii-research-program/

/sft/part-vii-research-program/
  previous: /sft/part-vi-case-studies/
  next:     /archsig/
```

SFT の章単位分割は v1 では行わない。
Part ページが長くなりすぎた場合に限り、章単位 route を追加する。

### ArchSig

ArchSig は manual / reference section としてページネーションする。

```text
/archsig/
  previous: /sft/part-vii-research-program/
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

### Outreach / Profile

ArchSig manual 以降は hub page として扱う。

```text
/outreach/
  previous: /archsig/roadmap/
  next:     /profile/

/profile/
  previous: /outreach/
  next:     /
```

## Page Template Requirements

各ページは次を持つ。

- global navigation
- page title
- short abstract / page role
- local table of contents, when the page is long
- canonical source link to `docs/` or GitHub
- previous / next navigation, when the page belongs to a reading sequence
- claim boundary note, when formal / tooling / empirical levels may be confused

## ArchSig Page Source Mapping

ArchSig page は、`docs/tool/` と `tools/archsig/docs/` の両方を source として使う。

| Website page | Primary source documents | Role |
| --- | --- | --- |
| `/archsig/` | `tools/archsig/README.md`, `docs/tool/README.md`, `docs/tool/principles.md` | Manual landing and conceptual boundary. |
| `/archsig/getting-started/` | `tools/archsig/README.md` | Minimal command path for first run. |
| `/archsig/commands/` | `tools/archsig/docs/commands.md` | CLI command reference. |
| `/archsig/artifacts/` | `tools/archsig/docs/artifacts-and-boundaries.md`, `docs/tool/signature_artifacts.md`, `docs/tool/reports.md`, `docs/tool/air.md` | Artifact and report reference. |
| `/archsig/boundaries/` | `tools/archsig/docs/artifacts-and-boundaries.md`, `docs/tool/claim_boundary.md`, `docs/tool/theorem_preconditions.md` | Measurement / claim boundary reading rules. |
| `/archsig/workflows/` | `docs/tool/workflows.md`, `tools/archsig/README.md` | Adoption, PR review, scheduled scans, dynamics workflows. |
| `/archsig/schemas/` | `docs/tool/schema_compatibility.md`, `docs/tool/air.md`, `docs/tool/signature_artifacts.md` | Schema versioning and compatibility reference. |
| `/archsig/operational-feedback/` | `tools/archsig/docs/operational-feedback.md`, `docs/tool/reports.md` | B10 operational feedback artifacts and reading rules. |
| `/archsig/examples/` | `docs/tool/examples.md`, `docs/tool/repair_suggestion.md` | Report examples and repair suggestion reading. |
| `/archsig/roadmap/` | `docs/tool/roadmap.md` | Tooling roadmap and standardization targets. |

ArchSig reference pages must keep these warnings visible:

- `archsig` is not a Lean prover.
- tool output is not a Lean theorem.
- extractor output is not a complete `ComponentUniverse`.
- measured zero is different from unmeasured.
- policy pass does not imply architecture lawfulness.
- report warning does not imply incident causality.

## Current Implementation Status

```text
implemented:
  /
  /aat/
  /aat/foundations/
  /aat/laws-and-witnesses/
  /aat/signature-and-boundary/
  /aat/local-law-packages/
  /aat/calculus-and-extensions/
  /aat/repair-and-dynamics/
  /aat/representations-and-effects/
  /aat/examples-and-boundaries/
  /aat/status/

planned:
  /profile/
  /interface/
  /sft/
  /sft/part-i-new-object/
  /sft/part-ii-basis/
  /sft/part-iii-core/
  /sft/part-iv-principles/
  /sft/part-v-computing-systems/
  /sft/part-vi-case-studies/
  /sft/part-vii-research-program/
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
```

## Later SEO Sitemap

公開ドメインが決まった後で、別途 `sitemap.xml` を作る。
その時点では、この設計図の route を URL 化し、GitHub Pages の公開 root から参照できるようにする。
