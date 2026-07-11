# Website Design

この文書は、AAT / SFT / ArchSig 公開サイトの設計方針、読者導線、ページネーション、
本文成熟度、source mapping を管理する。

- route と役割の一覧は [SITEMAP.md](SITEMAP.md) に置く。
- stack(Eleventy)、path rule、CSS 分割規律、preview は [guideline.md](guideline.md) を正とする。
- リニューアル全体の設計とウェーブ計画は
  [docs/note/website_renewal_design_note.md](../note/website_renewal_design_note.md) を正とする。

## 基本方針

- `docs/` は source of truth、`website/` は public reading surface として扱う。
- 公開サイトの source of truth は英語とし、prefix なしの route に置く。
  日本語は Qiita、Zenn、Hashnode などの outreach article として扱い、site mirror は作らない。
- AAT の数学的正典は `docs/aat/algebraic_geometric_theory/`(第I〜X部+付録)である。
  `website/aat/**` はこれを置き換えず、正典に忠実な web-native publication edition として扱う。
- AAT website は正典第I〜X部と 1:1 のルート構成をとる(Wave 1 で移行中)。
  website 独自の theorem claim は置かず、理論上の新規 claim は先に正典へ反映する。
- 数学本文、Lean status、proof obligation、tooling claim、empirical hypothesis を混同しない。
  claim taxonomy(Formal theorem / Certified bounded inference / Analytic reading)は
  AAT landing で一度説明し、各章はバッジと status card で参照する。
- SFT は `docs/sft/software_field_theory.md`(v2)に忠実な research monograph として扱う。
  v2 の P4 / P5 が完了するまで、website の SFT ページは v1 構成のまま凍結する(Wave 2)。
- ArchSig は standalone manual / reference section として扱う。CLI・schema の具体は
  v0.5.0 出荷後に確定させる(Wave 3)。v0.4.0→v0.5.0 で不変の概念・責務境界・
  theorem anchor は Wave 1 で先行執筆してよい。
- AAT / SFT ページは marketing summary ではなく、定義、前提、theorem boundary、
  例、反例、Lean status への接続を持つ技術本文として書く。
- 公開 theory pages の docs への参照は commit-pinned GitHub URL を使う。

## トップレベル route 設計

### AAT(正典 1:1、Wave 1)

```text
/aat/                             Overview: 正典宣言、中心図式(SVG)、claim taxonomy、部索引
/aat/atoms-objects-laws/          I.    Atom 公理系、atom family、configuration、architecture object、law、obstruction circuit
/aat/sites-and-sheaves/           II.   architecture context category、AAT site、cover、restriction、sheaf、descent の問い
/aat/law-algebra-lawful-locus/    III.  law algebra 層 O_X^U、obstruction ideal I_Ob^U、affine chart、scheme、lawful locus
/aat/obstruction-cohomology/      IV.   Čech 複体、obstruction cohomology、local lawful と global lawful の差
/aat/derived-geometry-repair/     V.    (W1b)lawful loci の交差、repair の derived 変形
/aat/singularity-monodromy-stack/ VI.   (W1b)Tor conflict、monodromy、decomposition stack / gerbe
/aat/representations-periods/     VII.  (W1b)graph / matrix / signature / period / distance の窓
/aat/measurement-theory/          VIII. (W1b)有限 measurement profile、unmeasured ≠ zero
/aat/evolution-geometry/          IX.   (W1b)trace category、temporal coefficient、Lyapunov reading
/aat/semantic-repair-saga/        X.    (W1b)SAGA: repair gluing = descent、SAGA 比較定理
/aat/appendix/                    付録  (W1b)ambient convention、標準AGへの埋め込み、worked example
/aat/related-work/                関連研究と novelty boundary(W1b で AG 語彙へ改訂)
/aat/status/                      Lean status(AG 索引・proof obligations 台帳を典拠。W1b で改訂)
/aat/formal-anchors/              Lean declarations の audit index(W1b で AG 基準へ改訂)
```

旧 classical 構成のルートのうち、atoms / architecture-objects / laws /
obstruction-circuits / zero-curvature は Wave 1a で削除し、`website/src/_redirects` で
新章へ 301 する。architecture-signature / design-principle-layers /
operations-and-calculus / dynamics-and-geometry / representations-and-effects /
canonical-examples-and-readings は Wave 1b で後継章へ 301 する(それまで残置)。

### SFT(v1 凍結中、Wave 2 で v2 構成へ)

現行の三部構成(field-and-force / computation / software-evolution / references、
計 20 route)は v1 のまま整合しており、Wave 2 発火(SFT P4 / P5 完了)まで変更しない。
v2 の route 設計は発火時の計画で確定する。

### ArchSig(Wave 1c で概念先行、Wave 3 で完成)

```text
/archsig/                  Skill-first landing(W1c で AG 計測 path 主軸に改訂)
/archsig/getting-started/  Skill onboarding(W3 で v0.5.0 基準の動く Quick Start へ)
/archsig/concepts/         (W1c 新設)三層責務、5値 verdict、measured ≠ unmeasured
/archsig/analyses/         (W1c 増強)evaluator カタログ+理論 anchor 対応表
/archsig/examples/         Skill request 例
/archsig/manual/           artifact の読み方(W3 で v0.5.0 語彙へ)
/archsig/reference/        CLI / schema(W3 で compare / gate / 単一契約版数へ)
/archsig/archview/         (W1c 新設)ArchView デモページ(seam-ignition サンプル)
```

### Outreach

`/outreach/` は外部記事への導線 hub。canonical technical pages へ戻る導線を置く。

## グローバルナビゲーション

```text
Home / AAT / SFT / ArchSig / Outreach
```

`_data/nav.json` で管理する。長い本文や章ページは landing から secondary navigation で辿る。

## 読書導線とページネーション

### AAT

読書順は正典の部順。prev / next は各ページの page-nav に置く。

```text
/aat/ -> I -> II -> III -> IV -> V -> VI -> VII -> VIII -> IX -> X -> appendix
  -> related-work -> status -> formal-anchors
```

Wave 1a 時点では IV が最後の実装章であり、IV の next は置かない
(V 実装時に W1b で接続する)。

### SFT / ArchSig / Outreach

SFT は v1 のページネーションを維持(Wave 2 で再設計)。
ArchSig は landing -> getting-started -> concepts -> analyses -> examples ->
manual -> reference -> archview の順(W1c 以降)。

## ページテンプレート要件

各ページは次を持つ(実装は `src/_layouts/base.njk` + ページ本文)。

- global navigation(layout が供給)
- page title / description / OGP(front matter が供給)
- article-hero(eyebrow、h1、lede)
- local table of contents(toc-panel、長いページのみ)
- previous / next(page-nav、読書順に属するページのみ)
- claim boundary note(formal / tooling / empirical の混同が起きうる箇所のみ)

### AAT publication edition の型

各章は正典の全節を、次の型で展開する。

```text
Definition
-> Lemma / Proposition / Theorem
-> Proof idea
-> Example
-> Counterexample / Non-conclusion
-> Lean status
```

- 正典の theorem label(定義 I.2.1 → Definition I.2.1)をそのまま使い、
  website 独自のラベル・主張を発明しない。
- theorem-grade claim は theorem-card / lean-status-card で命題名、Lean 名、
  status、仮定、境界を近接表示する。
- Lean status バッジは `lean_theorem_index_ag_aat.md` に対応行がある場合だけ表示する。
  status 語彙は現行status overlayの三分化
  (`proved` / `packaged (assumption-relative)` / `statement-only`)+ `defined only` に従う。
- 数学本文への commit-pinned link は各章のサイドバーに置かず、リファレンス面に集約する。
  Lean index・proof-obligation ledger・status overlay は更新される現行status面なので、同じリファレンス面から
  `main` 上の現行文書へリンクする。正式なリファレンス面は `/aat/status/` の
  Canonical sources とする。

## ArchSig page の参照元対応

| Website page | Primary source documents | Role |
| --- | --- | --- |
| `/archsig/` | `tools/archsig/README.md`, `docs/tool/README.md` | Skill-first landing。 |
| `/archsig/getting-started/` | `tools/archsig/README.md`, `tools/archsig/skills/*/SKILL.md` | Skill onboarding。 |
| `/archsig/concepts/`(W1c) | `docs/tool/README.md`, `tools/archsig/src/ag_measurement.rs`(verdict 語彙) | 三層責務、5値 verdict、境界規律。 |
| `/archsig/analyses/` | `tools/archsig/src/analysis/`(ag.* evaluator 群), 正典第IV〜VIII部 | evaluator カタログ+理論 anchor。 |
| `/archsig/examples/` | `tools/archsig/README.md`, `archsig-reader` Skill docs | 依頼→findings の読み例。 |
| `/archsig/manual/` | `tools/archsig/docs/`, `docs/tool/archsig_analysis_packet.md` | artifact reading manual。 |
| `/archsig/reference/` | `tools/archsig/docs/commands.md`(W3 で v0.5.0 基準) | command / schema reference。 |
| `/archsig/archview/`(W1c) | `tools/archview/README.md`, `tools/archview/archview.html` | 幾何 projection デモ。 |

ArchSig reference pages では次の境界を可視に保つ:
archsig は Lean 証明器ではない / tool output は Lean theorem ではない /
measured zero と unmeasured は異なる / policy pass は architecture lawfulness を意味しない。

## 本文成熟度

| Section | Route status | 成熟度 | 残作業 |
| --- | --- | --- | --- |
| `/aat/` landing | 実装済み | 正典宣言・中心図式・claim taxonomy・部索引 | 正典改訂時に同期 |
| `/aat/` Part I〜IV | 実装済み | 正典第I〜IV部の publication edition | 正典改訂時に同期 |
| `/aat/` Part V〜X+付録 | 実装済み | 正典第V〜X部と付録の publication edition | 正典改訂時に同期 |
| `/aat/related-work/`, `/aat/status/`, `/aat/formal-anchors/` | 実装済み | AG 基準の関連研究・status・形式化アンカー | 台帳更新時に同期 |
| `/sft/**` | 実装済み | SFT publication edition | SFT本文改訂時に同期 |
| `/archsig/**` | 実装済み | Skill-first overview、analyses、examples、manual、reference | tooling契約更新時に同期 |
| `/outreach/` | 実装済み | 外部記事 hub | 記事追加時に更新 |

## phase 管理

phase は renewal note の Wave 番号で管理する(旧 W2〜W4 表記は廃止)。

```text
Wave 0(完了 2026-07-05): Eleventy 化、CSS 分割、タイポグラフィ再配分、docs 同期
Wave 1a/1b(完了): AAT landing、第I〜X部、付録、status、formal anchors
Wave 1c/3(完了): ArchSig Skill-first overview、analyses、examples、manual、reference
Wave 2(完了): SFT publication edition
```

## SEO / sitemap

公開ドメインは `iroha1203.dev`。`sitemap.xml` / `llms.txt` は Eleventy collections から
自動生成される(手動同期なし)。旧ルートの 301 は `website/src/_redirects` で管理する。
