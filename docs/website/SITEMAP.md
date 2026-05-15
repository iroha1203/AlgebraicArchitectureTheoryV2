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
| `/aat/signature-and-boundary/` | `website/aat/signature-and-boundary/index.html` | AAT Part III. Signature and Theorem Boundary。 |
| `/aat/local-law-packages/` | `website/aat/local-law-packages/index.html` | AAT Part IV. Local Law Packages。 |
| `/aat/calculus-and-extensions/` | `website/aat/calculus-and-extensions/index.html` | AAT Part V. Calculus and Extensions。 |
| `/aat/repair-and-dynamics/` | `website/aat/repair-and-dynamics/index.html` | AAT Part VI. Repair and Dynamics。 |
| `/aat/representations-and-effects/` | `website/aat/representations-and-effects/index.html` | AAT Part VII. Representations and Effects。 |
| `/aat/examples-and-boundaries/` | `website/aat/examples-and-boundaries/index.html` | AAT Part VIII. Examples and Boundaries。 |
| `/aat/related-work/` | `website/aat/related-work/index.html` | AAT related work and novelty boundary。 |
| `/aat/status/` | `website/aat/status/index.html` | AAT Lean status、proof obligations、proved / defined only / future obligation の読み方。 |
| `/interface/` | `website/interface/index.html` | AAT -> SFT interface、片方向依存、claim translation、禁止される読み替え。 |
| `/sft/` | `website/sft/index.html` | SFT landing、Part 一覧、computable core、claim boundary への入口。 |
| `/sft/part-i-new-object/` | `website/sft/part-i-new-object/index.html` | SFT Part I. The New Object。 |
| `/sft/part-ii-basis/` | `website/sft/part-ii-basis/index.html` | SFT Part II. Algebraic and Observational Basis。 |
| `/sft/part-iii-core/` | `website/sft/part-iii-core/index.html` | SFT Part III. SFT Core。 |
| `/sft/part-iv-principles/` | `website/sft/part-iv-principles/index.html` | SFT Part IV. Principles and Theorems。 |
| `/sft/part-v-computing-systems/` | `website/sft/part-v-computing-systems/index.html` | SFT Part V. Computing Systems Built from SFT。 |
| `/sft/part-vi-case-studies/` | `website/sft/part-vi-case-studies/index.html` | SFT Part VI. Case Studies。 |
| `/sft/part-vii-research-program/` | `website/sft/part-vii-research-program/index.html` | SFT Part VII. Non-Conclusions and Research Program。 |
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
