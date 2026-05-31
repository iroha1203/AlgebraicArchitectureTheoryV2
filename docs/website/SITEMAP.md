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
| `/aat/` | `website/aat/index.html` | AAT landing、Atom-first の読書順、章クラスタ、Lean status / formal anchors への入口。 |
| `/aat/atoms/` | `website/aat/atoms/index.html` | AAT Part I. Foundations。Atom and primitive architectural facts。 |
| `/aat/architecture-objects/` | `website/aat/architecture-objects/index.html` | AAT Part I. Foundations。Molecules、ArchitectureObject、selected presentation、finite universe。 |
| `/aat/laws/` | `website/aat/laws/index.html` | AAT Part I. Foundations。DesignLaw、law universe、invariant family、lawfulness bridge。 |
| `/aat/obstruction-circuits/` | `website/aat/obstruction-circuits/index.html` | AAT Part II. Key Concepts。ObstructionCircuit、minimal bad molecule、finite witness universe。 |
| `/aat/zero-curvature/` | `website/aat/zero-curvature/index.html` | AAT Part II. Key Concepts。Flatness、ZeroCurvature、ZeroCurvaturePackage。 |
| `/aat/architecture-signature/` | `website/aat/architecture-signature/index.html` | AAT Part II. Key Concepts。Architecture Signature、multi-axis diagnostic、AATCore bridge、ArchSig boundary。 |
| `/aat/design-principle-layers/` | `website/aat/design-principle-layers/index.html` | AAT Part II. Key Concepts。SOLID、Layered / Clean Architecture、Event Sourcing、Saga、Circuit Breaker、Replicated Log as law packages。 |
| `/aat/operations-and-calculus/` | `website/aat/operations-and-calculus/index.html` | AAT Part II. Key Concepts。ArchitectureOperation、operation laws、feature extension、selected repair、synthesis soundness。 |
| `/aat/dynamics-and-geometry/` | `website/aat/dynamics-and-geometry/index.html` | AAT Part III. Geometry and Analytic Connections。ArchitecturePath、signature trajectory、PathHomotopy、DiagramFiller、selected monodromy / continuation。 |
| `/aat/representations-and-effects/` | `website/aat/representations-and-effects/index.html` | AAT Part III. Geometry and Analytic Connections。Graph、thin category、walk / matrix、analytic representation、state-transition algebra、effect law surface。 |
| `/aat/canonical-examples-and-readings/` | `website/aat/canonical-examples-and-readings/index.html` | AAT Part III. Geometry and Analytic Connections。Atom / molecule / law / circuit、coupon extension、static-flat semantic obstruction、repair transfer、SOLID counterexamples。 |
| `/aat/related-work/` | `website/aat/related-work/index.html` | AAT References。Related work and novelty claim。 |
| `/aat/status/` | `website/aat/status/index.html` | AAT Lean status、proof obligations、proved / defined only / future obligation の読み方。 |
| `/aat/formal-anchors/` | `website/aat/formal-anchors/index.html` | AAT 章の public claims と代表 Lean declarations の audit index。 |
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
| `/sft/references/` | `website/sft/references/index.html` | SFT reference appendix。formal anchors、research program、glossary への入口。 |
| `/sft/references/formal-anchors/` | `website/sft/references/formal-anchors/index.html` | SFT formal anchors。Lean status、formalized carriers、theorem-shaped surfaces。 |
| `/sft/references/research-program/` | `website/sft/references/research-program/index.html` | SFT research program。workbench、calibration、AI governance benchmark、closed-loop tooling へ進む研究計画。 |
| `/sft/references/glossary/` | `website/sft/references/glossary/index.html` | SFT glossary。field、force、attractor、ForecastCone、ConsequenceEnvelope などの用語境界と参照先。 |
| `/archsig/` | `website/archsig/index.html` | ArchSig v0.3.0 の Skill-first architecture analysis landing。 |
| `/archsig/getting-started/` | `website/archsig/getting-started/index.html` | LLM Skill onboarding、prompt examples、Skill が作る ArchMap / LawPolicy / analysis output。 |
| `/archsig/analyses/` | `website/archsig/analyses/index.html` | Boundary movement、responsibility drift、semantic coupling、order sensitivity、hotspots、missing evidence の分析カタログ。 |
| `/archsig/examples/` | `website/archsig/examples/index.html` | Skill request から returned findings / repair candidates / confirmation checks までの短い例。 |
| `/archsig/manual/` | `website/archsig/manual/index.html` | `analysis-summary`、analysis packet、measurement families、coverage gap、measurement basis の読み方。 |
| `/archsig/reference/` | `website/archsig/reference/index.html` | `analyze` primary workflow、command、schema、compatibility、artifact reference。 |
| `/outreach/` | `website/outreach/index.html` | Outreach article index と canonical technical pages への戻り導線。 |

## sitemap 対応ルール

- `website/sitemap.xml` には上記 route を `https://iroha1203.dev/` base で列挙する。
- route を追加・削除・rename した場合は、この文書と `website/sitemap.xml` を同時に更新する。
- `website/sitemap.xml` には `docs/website/` や GitHub repository 内部文書を載せない。
- source document への GitHub link は sitemap ではなく、各公開ページ本文の canonical source link として扱う。
