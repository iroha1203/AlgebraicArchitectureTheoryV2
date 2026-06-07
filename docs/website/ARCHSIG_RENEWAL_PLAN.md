# ArchSig Website Renewal Plan

この文書は、ArchSig website を **Web PR 面 & マニュアル** として
章立てから書き直すための計画書である。

目的は、ArchSig を研究仕様の説明ページとしてではなく、LLM Skill を通じて
すぐ使える architecture analysis surface として提示することにある。

## Core Position

ArchSig の website は、最初に次を伝える。

```text
Use an ArchSig Skill.
The Skill reads a codebase, authors ArchMap evidence, selects a LawPolicy,
runs ArchSig, reads the resulting measurements, inspects the code, and returns
review findings or repair candidates that engineers can act on.
```

公開ページの前半では、内部境界や non-conclusion を先に並べない。
主語は常に、ArchSig が何を出力できるか、何を読めるようにするか、
どの分析に使えるかに置く。

優先する表現:

- ArchSig can produce ...
- ArchSig computes ...
- ArchSig surfaces ...
- ArchSig connects ...
- ArchSig turns ArchMap and LawPolicy into ...

避ける表現:

- 否定を見出しや導入文の主語にする。
- 境界説明を前半の主要 value proposition より先に置く。
- non-conclusion を product copy の中心にする。

境界、measurement basis、coverage、reading strength は削らない。
ただし、前半の PR copy ではなく、後半の trust / reference / manual section で
結果を読むための補助情報として扱う。

## Audience

主読者は次の順で想定する。

1. LLM Skill を使って codebase analysis を依頼したい開発者。
2. PR review や architecture review に ArchSig を導入したいチーム。
3. AI-generated code の architecture movement を観測したいレビュアー。
4. ArchSig artifact、schema、command、AAT / SFT boundary を詳しく読みたい実装者。

最初の読者に CLI command や JSON schema を覚えさせない。
コマンドは Skill、debug、reproducibility のための後半 reference として扱う。

## Front-Half Message

ArchSig website の前半は、次の三点を強調する。

### 1. Skill を叩くだけで使える

ArchSig は human-operated CLI ではなく、LLM-native architecture analysis tool
として提示する。

`archsig-analysis-summary.json` や packet detail を人間向け onboarding の主画面にしない。
それらを正しく読むには AAT / ArchSig の measurement vocabulary が必要になり、
通常のエンジニアにとって入口の敷居が高くなりすぎる。

product experience では、LLM Skill が summary と packet refs を読み、
実コードと照合し、エンジニアには review findings、修正候補、確認ポイントとして返す。
LLM 解釈には hallucination risk が残るが、Skill 経由の手軽さと実コード照合による
実用性を優先する。

人間が直接やること:

- repo を指定する。
- `archmap-creater`、`law-policy-creater`、`archsig-reader` の 3 Skills を叩く。
- Skill が返す review findings、修正候補、確認ポイントを見る。

Skill が行うこと:

- selected source evidence を読む。
- `archmap-creater` Skill で `archmap/v1` を authoring する。
- `law-policy/v1` を合成する。
- ArchSig `analyze` を実行する。
- validation、`archsig-analysis-summary.json`、viewer data、packet refs、coverage repair queue を読む。
- 必要な実コードを再検査する。
- review findings、修正候補、確認ポイントを返す。
- 必要に応じて `pr-review` または FieldSig handoff へ進める。

### 2. コードベースの様々な分析ができる

ArchSig は PR comment generator ではなく、codebase architecture analysis surface
として提示する。

前半で見せる分析例:

- Which service, module, or feature boundary is getting crossed.
- Which files and responsibilities reviewers should inspect first.
- Whether a new feature is reaching into another feature's internals.
- Where business rules or workflow assumptions are duplicated, hidden, or moved.
- Which adapters, caches, providers, queues, or jobs are creating operational coupling.
- Which contracts, tests, docs, or traces support the architecture reading.
- Which expected evidence is missing before the analysis should be trusted.
- Whether two implementation paths preserve the same visible behavior.
- Whether changing the order of two operations changes architecture-relevant behavior.
- Which hotspots keep concentrating review pressure across the codebase.
- Which PR-local signals should become review comments or follow-up tasks.
- Which current-state findings should be handed to FieldSig for evolution analysis.

### 3. 既存解析ツールとの違い

ArchSig は既存ツールを置き換えるのではなく、観測・解釈・測定を接続する。

比較軸:

| Tool family | What it mainly sees | ArchSig adds |
| --- | --- | --- |
| Linter | local rule violations | architecture measurements under selected laws |
| Static analyzer | syntax, type, dataflow, dependency facts | source-grounded architecture observations and witness readings |
| Dependency graph | edges between modules | semantic coupling, law-relative obstruction, support, coverage, path readings |
| Metrics dashboard | aggregate trends | evidence-backed review findings and repair candidates |
| Generic AI review | free-form comments | ArchMap evidence, LawPolicy, validation, packet refs, measurement families |

この比較は競合比較ではなく、組み合わせ方を示すために使う。
ArchSig は linter、static analyzer、dependency graph、test、AI review と
一緒に使うことで、既存の technical evidence を architecture review の
source-grounded measurement へ接続する。

## Site Information Architecture

既存 `/website/archsig/` は公開中の current surface として維持する。
新版はまず `/website/archsig2/` に並行構築し、完成後に公開 path を
`/archsig/` へ差し替える。

移行中は `/archsig2/` を staging route として扱う。
`docs/website/SITEMAP.md`、`website/sitemap.xml`、`website/llms.txt` へ
正式公開 route として載せるのは、最終差し替え時に行う。

以下の IA では最終公開後の route 名として `/archsig/...` を書く。
実装中は同じ構成を `/archsig2/...` に作る。

### Compact Page Set

初版の `archsig2` はページを増やしすぎない。
旧版の細かい manual route を引き継がず、まず 6 ページ程度で
Web PR 面と実用マニュアルを成立させる。

- `/archsig/`
  - 軽い Web PR landing。
  - ArchSig は LLM Skills で使う architecture analysis tool だと即座に伝える。
  - repo を指定 -> 3 Skills を叩く -> findings を見る、の最短導線だけを見せる。
  - 詳細ページへの compact links を置く。
- `/archsig/getting-started/`
  - command tutorial ではなく Skill-first onboarding。
  - prompt examples。
  - human が Skill に渡すもの。
  - Skill が内部で作る ArchMap / LawPolicy / analysis output。
  - Skill が analysis output を読んで実コードを再検査し、human へ返す findings。
- `/archsig/analyses/`
  - ArchSig でできる codebase analysis のカタログ。
  - boundary crossing、responsibility movement、semantic coupling、feature extension、
    operation order sensitivity、hotspots、missing evidence、FieldSig handoff などを
    実務の言葉で説明する。
  - 既存解析ツールとの違いと組み合わせ方もここで独立セクションとして扱う。
- `/archsig/examples/`
  - Skill request から output までの短い examples。
  - payment boundary erosion。
  - coupon feature extension。
  - operation order sensitivity。
  - coverage repair queue。
- `/archsig/manual/`
  - 出力の読み方、主要 artifact、v1 derived measurement families、measurement basis を
    一つの manual page にまとめる。
  - `archsig-analysis-summary.json` は Skill / LLM の first reading surface として説明する。
  - `archsig-analysis-packet/v1` は optional raw detail evidence store として説明する。
  - measurement family の正式名はここで扱う。
- `/archsig/reference/`
  - command / schema / compatibility / detailed artifact reference。
  - `analyze` を primary workflow entry として書く。
  - `llm-native-workflow` / `north-star-workflow` は removed runtime surface として扱う。

旧版にある `/why/`, `/inputs/`, `/workflows/`, `/artifacts/`,
`/reading-output/`, `/anatomy/`, `/boundaries/`, `/archmap/`, `/air/`,
`/semantic-air/`, `/commands/`, `/schemas/`, `/operational-feedback/` は、
初版の `archsig2` では個別ページにしない。
必要な内容だけを上記 6 ページへ統合する。

将来、本文が重くなった場合だけ `/manual/` や `/reference/` から分割する。

## Top Page Rewrite Sketch

`/archsig/` は次の章立てにする。

1. Hero
   - H1 は `ArchSig` または `Architecture analysis through LLM Skills.`
   - lede は Skill-first かつ短くする。
2. Three-Step Start
   - repo を指定する。
   - `archmap-creater`、`law-policy-creater`、`archsig-reader` を叩く。
   - findings を見る。
3. What You Get Back
   - review findings、repair candidates、code refs、confirmation points。
4. First Workflow
   - Ask Skill -> ArchMap -> LawPolicy -> analyze -> Skill reads output -> code inspection -> findings。
5. Where To Go Next
   - Getting Started / Analyses / Examples / Manual / Reference。

トップには既存解析ツールとの比較を置かない。
その話は `/archsig/analyses/` の独立 section に置き、linter、static analyzer、
dependency graph、test、AI review と組み合わせることで価値が出ると説明する。

## Getting Started Rewrite Sketch

`/archsig/getting-started/` はコマンド軸から Skill 軸へ全面改稿する。

1. Start With A Skill Request
   - prompt examples を置く。
2. Tell The Skill What To Inspect
   - scope、goal、risk focus、available evidence、excluded readings。
3. What The Skill Builds
   - ArchMap、LawPolicy、analysis packet、summary。
4. What The Skill Returns
   - measurement summary そのものではなく、LLM が summary と packet refs を読んだ後の findings。
   - repair candidates、code refs、confirmation points、追加調査ポイント。
5. Improve The Request
   - broad inspection、PR-local inspection、boundary-focused inspection、homotopy/path-focused inspection。
6. When To Open The Manual
   - artifacts、measurement、commands、schemas。

## Writing Rules

前半の copy:

- 読者にできることを先に書く。
- Skill に頼む自然な文を使う。
- 出力名は必要なときだけ出す。
- theoretical boundary は結果を読むための補助として後半に置く。
- defensive copy を避ける。

後半の manual:

- artifact 名、schema 名、command 名を正確に書く。
- `analyze` を primary workflow entry として扱う。
- `llm-native-workflow` / `north-star-workflow` は removed runtime surface として扱う。
- `ArchMap` は law-independent observation。
- `law-policy/v1` は current JSON name for selected evaluator profile。
- `archsig-analysis-summary.json` は Skill / LLM の first reading surface。
- `archsig-analysis-packet/v1` は optional raw detail evidence store。
- `pr-review` と FieldSig handoff は役割を分ける。

## Implementation Phases

### Phase 1: Planning And Staging Surface

- この計画書を追加する。
- `website/archsig2/` を staging directory として作る。
- `/archsig2/` を Skill-first Web PR landing として作る。
- `archsig2` 内の sidebar / manual map の章順を更新する。
- 既存 `/archsig/` はこの phase では変更しない。

### Phase 2: Skill-First Onboarding

- `/archsig2/getting-started/` を作る。
- `/archsig2/analyses/` の骨格を作る。
- 既存 `/archsig/...` はこの phase では変更しない。

### Phase 3: Output And Measurement

- `/archsig2/manual/` を Skill が読む output と human に返す findings の関係を説明する manual として作る。
- `/archsig2/examples/` を Skill request -> result examples として作る。
- 既存 `/archsig/...` はこの phase では変更しない。

### Phase 4: Workflows And Reference

- `/archsig2/reference/` を command / schema / compatibility reference として作る。
- `/archsig2/`、`/archsig2/getting-started/`、`/archsig2/analyses/`、
  `/archsig2/examples/`、`/archsig2/manual/`、`/archsig2/reference/` の
  page nav を揃える。
- 既存 `/archsig/...` はこの phase では変更しない。

### Phase 5: Route And QA

- route 追加や rename があれば `docs/website/SITEMAP.md` を更新する。
- staging 中の `/archsig2/` は public sitemap に載せない。
- local server で preview する。
- `archsig2` pages の title、link、asset path、layout、overflow を確認する。
- `git diff --check` と hidden / bidirectional Unicode scan を実行する。

### Phase 6: Publish Swap

- 完成後に `website/archsig/` を新版へ差し替える。
- 移行後、旧版は archive / fallback path へ残さず削除する。
- `docs/website/SITEMAP.md`、`website/sitemap.xml`、`website/llms.txt` を
  正式 `/archsig/` route として更新する。
- `/archsig2/` staging route を削除するか、公開対象から外す。
- 最終 preview と link check を行う。

## Acceptance Criteria

- ArchSig website の前半が Skill-first になっている。
- Getting Started が command tutorial ではなく LLM Skill onboarding になっている。
- Top page が「何ができるか」「どう使うか」「何が返るか」「既存ツールと何が違うか」を先に示している。
- v1 derived measurement families が後半 manual で体系的に読める。
- 初版の `archsig2` が 6 ページ程度の compact page set に収まっている。
- command / schema / theoretical boundary は reference として読める位置にある。
- 前半の copy が defensive non-conclusion list になっていない。
- ArchSig / FieldSig / ArchMap / LawPolicy / analysis packet / analysis summary / LLM code inspection の責務が混ざっていない。
