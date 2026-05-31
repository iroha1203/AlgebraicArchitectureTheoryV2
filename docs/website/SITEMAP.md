# Website Sitemap

この文書は、公開 website の route と production sitemap の対応を管理する。
website の設計方針、読者導線、ページネーション、本文成熟度は
[DESIGN.md](DESIGN.md) に置く。

SEO 用の公開 `sitemap.xml` は `website/sitemap.xml` であり、この文書そのものではない。

## 公開設定

- 公開ドメイン: `iroha1203.dev`
- production base URL: `https://iroha1203.dev/`
- production sitemap: `website/sitemap.xml`
- robots file: `website/robots.txt`
- custom domain file: `website/CNAME`

`website/sitemap.xml` は、この文書の canonical public routes と一致させる。
`website/robots.txt` は `https://iroha1203.dev/sitemap.xml` を指す。

## Canonical Public Routes

英語版が canonical route である。
日本語は mirror route ではなく、outreach article への導線として扱う。

| Route | Source file | Role |
| --- | --- | --- |
| `/` | `website/index.html` | Top page、著者プロフィールの短い導入、AAT / SFT / ArchSig の入口、主要 article への導線。 |
| `/profile/` | `website/profile/index.html` | 著者プロフィール、連絡先、GitHub、公開活動。 |
| `/aat/` | `website/aat/index.html` | AAT landing、読む順序、章クラスタ、status / repository docs への入口。 |
| `/aat/foundations/` | `website/aat/foundations/index.html` | AAT Part I. Foundations。 |
| `/aat/laws-and-witnesses/` | `website/aat/laws-and-witnesses/index.html` | AAT Part II. Laws and Witnesses。 |
| `/aat/architecture-signature/` | `website/aat/architecture-signature/index.html` | AAT Part III. Architecture Signature。 |
| `/aat/local-law-packages/` | `website/aat/local-law-packages/index.html` | AAT Part IV. Local Law Packages。 |
| `/aat/calculus-and-extensions/` | `website/aat/calculus-and-extensions/index.html` | AAT Part V. Calculus and Extensions。 |
| `/aat/repair-and-dynamics/` | `website/aat/repair-and-dynamics/index.html` | AAT Part VI. Repair and Dynamics。 |
| `/aat/representations-and-effects/` | `website/aat/representations-and-effects/index.html` | AAT Part VII. Representations and Effects。 |
| `/aat/examples-and-boundaries/` | `website/aat/examples-and-boundaries/index.html` | AAT Part VIII. Examples and Boundaries。 |
| `/aat/related-work/` | `website/aat/related-work/index.html` | AAT related work and novelty boundary。 |
| `/aat/status/` | `website/aat/status/index.html` | AAT Lean status、proof obligations、proved / defined only / future obligation の読み方。 |
| `/sft/` | `website/sft/index.html` | SFT overview。短い abstract、章インデックス、status / glossary への入口。 |
| `/sft/field-and-force/` | `website/sft/field-and-force/index.html` | 1. Field and Force。開発組織全体を field of forces として記述する第1部の入口。 |
| `/sft/field-and-force/field/` | `website/sft/field-and-force/field/index.html` | 1-1. Field。コードベースと開発組織を、memory、artifact、agent、governance、feedback からなる development field として扱う。 |
| `/sft/field-and-force/force/` | `website/sft/field-and-force/force/index.html` | 1-2. Force。PRD、issue、spec、review、incident、AI proposal を future operation support に作用する artifact force として扱う。 |
| `/sft/field-and-force/organization/` | `website/sft/field-and-force/organization/index.html` | 1-3. Organization。開発者、AI agent、ownership、communication path、routine、recurrent path を field structure として扱う。 |
| `/sft/field-and-force/governance/` | `website/sft/field-and-force/governance/index.html` | 1-4. Governance。review、CI、operational feedback、governance が future support を更新することを扱う。 |
| `/sft/computation/` | `website/sft/computation/index.html` | 2. Making Software Evolution Computable。ソフトウェア進化を計算可能な対象にする第2部の入口。 |
| `/sft/computation/interface/` | `website/sft/computation/interface/index.html` | 2-1. Interface。SFT の field estimate を AAT projection、ArchSig observation、observation boundary へ接続する。 |
| `/sft/computation/computational-core/` | `website/sft/computation/computational-core/index.html` | 2-2. Computational Core。ArtifactAction、OperationSupport、OperationPolicy、StepRelation、bounded path を SFT 計算の中核として扱う。 |
| `/sft/computation/forecast-cone/` | `website/sft/computation/forecast-cone/index.html` | 2-3. ForecastCone。support と step semantics から、horizon 付きの bounded reachable futures を計算する。 |
| `/sft/computation/workbench/` | `website/sft/computation/workbench/index.html` | 2-4. Workbench。ForecastCone を ConsequenceEnvelope、proposal accounting、ArchSig artifact、calibration hook、計算問題へ接続する。 |
| `/sft/software-evolution/` | `website/sft/software-evolution/index.html` | 3. Software Evolution。governance、attractor engineering、AI proposal policy、lifecycle feedback により field を steer する第3部の入口。 |
| `/sft/software-evolution/field-shaping/` | `website/sft/software-evolution/field-shaping/index.html` | 3-1. Field Shaping。review、CI、type systems、runtime guards、ownership、feedback により support、policy、observation を変形する。 |
| `/sft/software-evolution/attractor-engineering/` | `website/sft/software-evolution/attractor-engineering/index.html` | 3-2. Attractor Engineering。stable regions、design levers、measurement surface により望ましい futures を自然にする。 |
| `/sft/software-evolution/ai-proposal-governance/` | `website/sft/software-evolution/ai-proposal-governance/index.html` | 3-3. AI Proposal Governance。AI-generated proposal support を theorem boundary、shortcut witness、review、CI の中で制御する。 |
| `/sft/software-evolution/lifecycle-closed-loop/` | `website/sft/software-evolution/lifecycle-closed-loop/index.html` | 3-4. Lifecycle and Closed-Loop Evolution。repair、migration、contraction、deletion、posterior update により evolution loop を閉じる。 |
| `/sft/formal-core/` | `website/sft/formal-core/index.html` | Formal Core。SoftwareField、OperationSupport、StepRelation、ForecastCone、cone projection、support safety、EnvelopeProjection など、定理になる部分。 |
| `/sft/theorem-candidates/` | `website/sft/theorem-candidates/index.html` | Theorem Candidates。SFT の theorem-shaped statements、counterexample anchors、Lean status、formalization target を一覧する参照ページ。 |
| `/sft/research-program/` | `website/sft/research-program/index.html` | Research Program。SFT workbench、calibration、AI governance benchmark、closed-loop tooling へ進む研究計画。 |
| `/sft/positioning/` | `website/sft/positioning/index.html` | Positioning and Non-Conclusions。SFT を static metric、process model、DevOps maturity model、socio-technical metaphor、technical debt taxonomy、AI benchmark、formal verification と混同しないための位置づけ。 |
| `/sft/status/` | `website/sft/status/index.html` | Status and Claim Boundaries。Lean status、claim level、non-conclusion、経験科学との境界を本編から分離して管理する付録。 |
| `/sft/glossary/` | `website/sft/glossary/index.html` | Glossary。field、force、attractor、ForecastCone、ConsequenceEnvelope などの用語境界と参照先。 |
| `/archsig/` | `website/archsig/index.html` | ArchSig manual landing、Core / Review / FieldSig handoff surface への入口。 |
| `/archsig/why/` | `website/archsig/why/index.html` | Why ArchSig? ArchSig の製品価値、レビューギャップ、AI-native development での位置づけ。 |
| `/archsig/getting-started/` | `website/archsig/getting-started/index.html` | LLM-native ArchMap / LawPolicy / ArchSig analysis packet の最短手順。 |
| `/archsig/ci/` | `website/archsig/ci/index.html` | CI / PR review 導入。ArchMap、LawPolicy、analysis packet、bounded projections、feature report、PR comment、review gate policy。 |
| `/archsig/inputs/` | `website/archsig/inputs/index.html` | Inputs and configuration。policy、runtime edge、PR metadata、proposal input の準備。 |
| `/archsig/reading-output/` | `website/archsig/reading-output/index.html` | Reading the Output。ArchMap、LawPolicy、analysis packet、validation、projection artifact、policy decision の読み方。 |
| `/archsig/anatomy/` | `website/archsig/anatomy/index.html` | The Anatomy of an Architecture Signal。ArchSig の中核思想を一枚で読むページ。 |
| `/archsig/air/` | `website/archsig/air/index.html` | AIR。ArchSig analysis state を claim、coverage、theorem precondition、review report へ接続する bounded projection。 |
| `/archsig/archmap/` | `website/archsig/archmap/index.html` | ArchMap。source-grounded Atom observation map。 |
| `/archsig/semantic-air/` | `website/archsig/semantic-air/index.html` | Semantic AIR。LLM semantic observation を ArchMap に記録し、bounded AIR claim へ投影する evidence boundary。 |
| `/archsig/commands/` | `website/archsig/commands/index.html` | ArchSig command reference。SFT / Operational commands は FieldSig へ移管。 |
| `/archsig/artifacts/` | `website/archsig/artifacts/index.html` | Artifact reference。 |
| `/archsig/boundaries/` | `website/archsig/boundaries/index.html` | Measurement / claim boundary の読み方。 |
| `/archsig/workflows/` | `website/archsig/workflows/index.html` | Workflow manual。 |
| `/archsig/schemas/` | `website/archsig/schemas/index.html` | Schema and compatibility reference。 |
| `/archsig/operational-feedback/` | `website/archsig/operational-feedback/index.html` | FieldSig operational feedback handoff。 |
| `/archsig/examples/` | `website/archsig/examples/index.html` | Examples and report reading。 |
| `/outreach/` | `website/outreach/index.html` | Outreach article index と canonical technical pages への戻り導線。 |

## Renewal Preview Routes

以下は公開 sitemap に載せない preview route である。完成後に canonical route へ昇格するまで、
`website/sitemap.xml` と `website/llms.txt` には追加しない。

| Route | Source file | Final canonical route | Role |
| --- | --- | --- | --- |
| `/aat2/` | `website/aat2/index.html` | `/aat/` | AAT renewal preview landing。Atom refoundation 後の章構成、読書順、claim boundary の入口。 |
| `/aat2/atoms/` | `website/aat2/atoms/index.html` | `/aat/atoms/` | AAT renewal preview Part I。Atom と primitive architectural facts の読者向け導入。 |
| `/aat2/architecture-objects/` | `website/aat2/architecture-objects/index.html` | `/aat/architecture-objects/` | AAT renewal preview Part I。Molecule、ArchitectureObject、selected presentation、finite universe の読者向け導入。 |
| `/aat2/laws/` | `website/aat2/laws/index.html` | `/aat/laws/` | AAT renewal preview Part I。DesignLaw、law universe、invariant family、lawfulness bridge の読者向け導入。 |
| `/aat2/obstruction-circuits/` | `website/aat2/obstruction-circuits/index.html` | `/aat/obstruction-circuits/` | AAT renewal preview Part I。ObstructionCircuit、minimal bad molecule、finite witness universe の読者向け導入。 |
| `/aat2/zero-curvature/` | `website/aat2/zero-curvature/index.html` | `/aat/zero-curvature/` | AAT renewal preview Part II。Flatness、ZeroCurvature、ZeroCurvaturePackage の読者向け導入。 |
| `/aat2/architecture-signature/` | `website/aat2/architecture-signature/index.html` | `/aat/architecture-signature/` | AAT renewal preview Part II。Architecture Signature、multi-axis diagnostic、AATCore bridge、ArchSig boundary の読者向け導入。 |

## sitemap 対応ルール

- `website/sitemap.xml` には上記 route を `https://iroha1203.dev/` base で列挙する。
- route を追加・削除・rename した場合は、この文書と `website/sitemap.xml` を同時に更新する。
- `website/sitemap.xml` には `docs/website/` や GitHub repository 内部文書を載せない。
- source document への GitHub link は sitemap ではなく、各公開ページ本文の canonical source link として扱う。
