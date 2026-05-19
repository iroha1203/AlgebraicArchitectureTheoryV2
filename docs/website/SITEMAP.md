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
| `/sft/field/` | `website/sft/field/index.html` | 1. The Development Organization as a Field。開発組織全体を field として記述する第1部の入口。 |
| `/sft/field/codebase-memory/` | `website/sft/field/codebase-memory/index.html` | 1-1. Codebase as Field Memory。要求、設計判断、review、CI、incident、ownership、tooling practice が codebase に記憶として沈着することを扱う。 |
| `/sft/field/artifacts/` | `website/sft/field/artifacts/index.html` | 1-2. Artifacts Shape the Field。PRD、spec、issue、design note、review comment、incident report を artifact-mediated force として読む。 |
| `/sft/field/agents/` | `website/sft/field/agents/index.html` | 1-3. Developers and AI Agents。人間の開発者と AI agent が artifact interpreter、proposal generator、local pattern amplifier として field に参加することを扱う。 |
| `/sft/field/organization-structure/` | `website/sft/field/organization-structure/index.html` | 1-4. Organization Structure as Field。Conway 的な communication path、ownership boundary、review route、approval flow が recurrent PR shape と architecture future を作ることを扱う。 |
| `/sft/field/governance-feedback/` | `website/sft/field/governance-feedback/index.html` | 1-5. Governance and Feedback。review、CI、type checker、runtime observation、incident、postmortem、lifecycle pressure が field memory を更新することを扱う。 |
| `/sft/field/architecture-futures/` | `website/sft/field/architecture-futures/index.html` | 1-6. Architecture Futures。field の下でどの architecture future が到達可能になるかを、endpoint ではなく trajectory、signature movement、default path として読む。 |
| `/sft/computation/` | `website/sft/computation/index.html` | 2. Making Software Evolution Computable。ソフトウェア進化を計算可能な対象にする第2部の入口。 |
| `/sft/computation/computable-slice/` | `website/sft/computation/computable-slice/index.html` | 2-1. Computable Slice。DevelopmentField から modeling boundary の下で SoftwareFieldEstimate を切り出し、SoftwareField と architecture projection を定める。 |
| `/sft/computation/aat-interface/` | `website/sft/computation/aat-interface/index.html` | 2-2. AAT / SFT Interface。AAT の local algebra、ArchitectureObject、ArchitectureOperation、InvariantFamily、ObstructionWitness、ArchitectureSignature を SFT の architecture projection、local premise、forecast boundary として片方向に読む。 |
| `/sft/computation/observation/` | `website/sft/computation/observation/index.html` | 2-3. Observation Layer。ArchSig により real artifact を AAT observables と SFT field estimate へ写し、signature、obstruction、theorem boundary、unknown remainder を観測可能にする。 |
| `/sft/computation/operation-support/` | `website/sft/computation/operation-support/index.html` | 2-4. Operation Support and Policy。どの operation が自然、低コスト、選ばれやすいものとして field に現れるかを計算対象にする。 |
| `/sft/computation/step-relation/` | `website/sft/computation/step-relation/index.html` | 2-5. StepRelation and Field Paths。supported operation による field transition と bounded path を扱う。 |
| `/sft/computation/forecast-cone/` | `website/sft/computation/forecast-cone/index.html` | 2-6. ForecastCone。未来を一点予測せず、field、support、policy、horizon の下で到達可能な未来の円錐として計算する。 |
| `/sft/computation/consequence-envelope/` | `website/sft/computation/consequence-envelope/index.html` | 2-7. ConsequenceEnvelope。ForecastCone を path class、affected axes、obstruction candidate、missing invariant、governance question の読める地図へ射影する。 |
| `/sft/computation/support-safety/` | `website/sft/computation/support-safety/index.html` | 2-8. Support Safety and Cone Narrowing。support inclusion、step simulation、safe region による cone projection と narrowing を扱う。 |
| `/sft/computation/proposal-accounting/` | `website/sft/computation/proposal-accounting/index.html` | 2-9. Proposal Accounting and Review Mediation。proposal pressure、accepted proposal、rejected proposal、review-mediated transition を分け、accepted change と future support を混同しない。 |
| `/sft/computation/computational-problems/` | `website/sft/computation/computational-problems/index.html` | 2-10. SFT Computational Problems。field reconstruction、support inference、envelope generation、cone narrowing、support safety、feedback update を計算問題として整理する。 |
| `/sft/computation/archsig-pipeline/` | `website/sft/computation/archsig-pipeline/index.html` | 2-11. ArchSig-SFT Pipeline。Markdown PRD / Spec / Issue / AI Proposal から ArtifactDescriptor、OperationSupportEstimate、ForecastConeSkeleton、ConsequenceEnvelope、calibration hook へ進む tooling surface。 |
| `/sft/computation/simulator-calibration/` | `website/sft/computation/simulator-calibration/index.html` | 2-12. Simulator and Calibration。PRD-to-ConsequenceEnvelope simulator の maturity level、forecast item と observed PR / review / CI / incident outcome の照合、calibrated claim への条件を扱う。 |
| `/sft/intervention/` | `website/sft/intervention/index.html` | 3. Field Intervention and Control。計算された future の到達可能性に対して、governance、feedback、policy design により介入する第3部の入口。 |
| `/sft/intervention/governance/` | `website/sft/intervention/governance/index.html` | 3-1. Governance as Field Shaping。review、CI、type checker、runtime guard、AI policy を future support と observation boundary を変える介入として扱う。 |
| `/sft/intervention/attractor-engineering/` | `website/sft/intervention/attractor-engineering/index.html` | 3-2. Attractor Engineering。良い future が自然に選ばれ、悪い shortcut が高コスト・観測可能・review-mediated になるよう field を設計する SFT の代表的応用。 |
| `/sft/intervention/stable-regions/` | `website/sft/intervention/stable-regions/index.html` | 3-3. Stable Regions and Recurrent Paths。DefaultPath、RecurrentPattern、StableRegion、ReachablePreimage を使い、attractor / basin 語彙を追加 semantics なしに強めない。 |
| `/sft/intervention/ai-governance/` | `website/sft/intervention/ai-governance/index.html` | 3-4. AI Proposal Governance。AI agent が生成する proposal support を bounded field model、theorem boundary、review / CI feedback の中で制御する。 |
| `/sft/intervention/lifecycle/` | `website/sft/intervention/lifecycle/index.html` | 3-5. Lifecycle Decisions。repair、migration、contraction、deletion、end-of-life を field capacity と architecture future の変化として比較する。 |
| `/sft/intervention/closed-loop/` | `website/sft/intervention/closed-loop/index.html` | 3-6. Closed-Loop Field Update。PR、review、CI、runtime feedback、incident outcome により field estimate を更新し、future support を再設計する。 |
| `/sft/formal-core/` | `website/sft/formal-core/index.html` | Formal Core。SoftwareField、OperationSupport、StepRelation、ForecastCone、cone projection、support safety、EnvelopeProjection など、定理になる部分。 |
| `/sft/theorem-candidates/` | `website/sft/theorem-candidates/index.html` | Theorem Candidates。SFT の theorem-shaped statements、counterexample anchors、Lean status、formalization target を一覧する参照ページ。 |
| `/sft/research-program/` | `website/sft/research-program/index.html` | Research Program。SFT workbench、calibration、AI governance benchmark、closed-loop tooling へ進む研究計画。 |
| `/sft/positioning/` | `website/sft/positioning/index.html` | Positioning and Non-Conclusions。SFT を static metric、process model、DevOps maturity model、socio-technical metaphor、technical debt taxonomy、AI benchmark、formal verification と混同しないための位置づけ。 |
| `/sft/status/` | `website/sft/status/index.html` | Status and Claim Boundaries。Lean status、claim level、non-conclusion、経験科学との境界を本編から分離して管理する付録。 |
| `/sft/glossary/` | `website/sft/glossary/index.html` | Glossary。field、force、attractor、ForecastCone、ConsequenceEnvelope などの用語境界と参照先。 |
| `/archsig/` | `website/archsig/index.html` | ArchSig manual landing、Core / Review / SFT / Operational surface への入口。 |
| `/archsig/getting-started/` | `website/archsig/getting-started/index.html` | ArchSig 最短手順。 |
| `/archsig/commands/` | `website/archsig/commands/index.html` | ArchSig command reference。 |
| `/archsig/artifacts/` | `website/archsig/artifacts/index.html` | Artifact reference。 |
| `/archsig/boundaries/` | `website/archsig/boundaries/index.html` | Measurement / claim boundary の読み方。 |
| `/archsig/workflows/` | `website/archsig/workflows/index.html` | Workflow manual。 |
| `/archsig/schemas/` | `website/archsig/schemas/index.html` | Schema and compatibility reference。 |
| `/archsig/operational-feedback/` | `website/archsig/operational-feedback/index.html` | Operational feedback manual。 |
| `/archsig/examples/` | `website/archsig/examples/index.html` | Examples and report reading。 |
| `/archsig/roadmap/` | `website/archsig/roadmap/index.html` | Tooling roadmap。 |
| `/outreach/` | `website/outreach/index.html` | Outreach article index と canonical technical pages への戻り導線。 |

## sitemap 対応ルール

- `website/sitemap.xml` には上記 route を `https://iroha1203.dev/` base で列挙する。
- route を追加・削除・rename した場合は、この文書と `website/sitemap.xml` を同時に更新する。
- `website/sitemap.xml` には `docs/website/` や GitHub repository 内部文書を載せない。
- source document への GitHub link は sitemap ではなく、各公開ページ本文の canonical source link として扱う。
