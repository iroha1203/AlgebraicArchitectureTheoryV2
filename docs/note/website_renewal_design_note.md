# Website リニューアル設計ノート

- 日付: 2026-07-05
- 対象: `website/`(iroha1203.dev、Cloudflare Pages 配信)
- 位置づけ: リニューアル全体の設計文書。実装 PRD はこのノートから分割して起こす。
- 関連: `docs/website/DESIGN.md`(現行設計)、`docs/website/AAT_RENEWAL_PLAN.md` /
  `SFT_REWRITE_PLAN.md` / `ARCHSIG_RENEWAL_PLAN.md`(前世代計画。本ノートが更新・置換する)

## 問い

**website を「古典 AAT の読書面」から「代数幾何版 AAT を正典とする研究出版面」へ、
正典側の成熟度差(AAT=確定 / SFT=v2 改訂中 / ArchSig=v0.5.0 設計中)に振り回されずに
移行するには、何をどの順で作り直すべきか?**

この問いから次の判定規律を得る。

- 正典が確定している領域(AAT AG 版)だけを今リライトし、動いている領域(SFT v2、
  ArchSig v0.5.0)は正典側の完了を待つ。website が正典より先行して claim を作らない。
- 基盤(テンプレート機構・CSS 分割・デザインシステム)はコンテンツと独立に先行できる。
  基盤刷新を後回しにすると、AAT リライトが旧基盤の上に積まれ二度手間になる。
- 「リッチにする」は装飾の追加ではなく、数学出版物としての読みやすさ
  (タイポグラフィ、定理環境の視覚言語、図式)への投資として判定する。

## 1. 現状診断(2026-07-05 棚卸し)

### 1.1 構成

- 43 ページ(すべて directory route + `index.html`)。トップ 1、`aat/` 15、`sft/` 20、
  `archsig/` 6、`outreach/` 1。
- `assets/site.css` 2769 行、`assets/site.js` 198 行。no-build 静的スタック。
- sitemap.xml / llms.txt / robots.txt は現状 43 ルートと整合(手動同期)。

### 1.2 課題(確認済みの事実)

| # | 課題 | 事実 |
| --- | --- | --- |
| C1 | 内容が古典 AAT | `aat/` 全 15 ページに scheme / sheaf / cohomology / descent 系語彙が 0 件。Atom → molecule → law → circuit → signature の旧定式化のまま。 |
| C2 | ArchSig が薄い | 6 ページとも H2 のみのフラット構成(H3 ゼロ)、151–183 行。概念説明中心で、動く例・artifact の読み方・理論 anchor が薄く製品マニュアルの密度にない。 |
| C3 | CSS 肥大化 | 2769 行が無コメント・無セクション。カスタムプロパティ 191 定義中、実使用は約 50 種。`.home-page` 上書きが全域に散在し、同一セレクタの分散定義が複数。 |
| C4 | テンプレート機構なし | ヘッダ / ナビ / フッター / OGP メタが 43 ページに物理コピペ。ナビ 1 項目の変更が 43 ファイル修正になる。 |
| C5 | SFT / ArchSig の鮮度 | SFT は v1(ForecastCone / ConsequenceEnvelope 中心)の三部構成。ArchSig は v0.4.0 以前の記述。どちらも正典側が改訂中。 |

### 1.3 資産(捨てないもの)

- ダークモード 3 層方式(OS 設定 / data-theme / localStorage)と FOUC 防止スクリプト。
- theorem-card / lean-status-card / boundary-note などの定理環境コンポーネント群。
  AG 版リライトでも視覚言語の核として再利用する。
- sitemap / llms.txt / robots の整合運用、OGP / JSON-LD、directory route 規約。
- `outreach/` の外部記事導線、トップの著者プロフィール。

## 2. 正典側の成熟度と同期戦略

リニューアルの最大の設計変数は、website ではなく正典側の状態である。

| 領域 | 正典 | 状態 | website が今書けること |
| --- | --- | --- | --- |
| AAT | `docs/aat/algebraic_geometric_theory/`(第I〜X部+付録) | **確定**。第X部 SAGA まで含め正典宣言済み。Lean は `lean_theorem_index_ag_aat.md` が status 供給源 | 全面リライト可能。今回の主戦場 |
| SFT | `docs/sft/software_field_theory.md`(v2) | 改訂中。第V・VII・VIII部が予告、README / aat_interface は v1 語彙のまま(P5 で同期予定) | 骨格の予告までは可能だが、本文リライトは P4/P5 完了待ち |
| ArchSig | `tools/archsig/README.md` + `docs/tool/` | v0.4.0 稼働中。ただし v0.5.0 再設計で CLI 名(pr-review → compare/gate)、フラグ、artifact 版数、後方互換が全面変更予定(PRD 未着手) | 概念・責務境界・5値 verdict・theory anchor は v0.4.0→v0.5.0 で不変なので先行執筆可。CLI / schema の具体は v0.5.0 出荷後 |

方針: **website の各領域は正典の完了イベントに紐づけて更新する**。website 側で
先回りした記述(v0.5.0 の未出荷コマンド、SFT 予告章の本文化)は作らない。

## 3. 全体設計: 4 ウェーブ

```text
Wave 0  基盤刷新(テンプレート機構、CSS 分割、デザインシステム)
          — コンテンツは現状のまま移設。見た目と保守性だけ変える
Wave 1  AAT 全面リライト(AG 版第I〜X部+付録+status)
          + ArchSig の「概念・責務境界」先行増強(版数非依存の章のみ)
Wave 2  SFT v2 リライト — 発火条件: SFT P4/P5 完了(README / interface の v2 同期)
Wave 3  ArchSig 製品マニュアル完成 — 発火条件: ArchSig v0.5.0 出荷
          (compare / gate、単一契約版数、SAGA evaluator、repair-plan)
```

Wave 0 と Wave 1 が今回の実作業(Claude 直接実装、§9)。Wave 2 / 3 は構成と
受け入れ条件だけ本ノートで固定し、発火条件が満たされた時点で改めて計画する。

## 4. Wave 0: 基盤刷新

### 4.1 テンプレート機構(確定: Eleventy SSG + Cloudflare Pages 連携ビルド)

2026-07-05 ユーザー決定。手製生成スクリプト(旧 A-1)・現状維持(旧 A-2)・
JS 挿入(旧 A-3)は不採用とし、**Eleventy(11ty)による SSG 化**で 43 ページへの
コピペ複製・sitemap / llms.txt の手動同期・prev-next の手書きを一括解消する。

決定理由:

- 手製スクリプトは front matter 解析、prev/next、dev server、partial と
  SSG の劣化再実装に向かう。リニューアル後のページ数増加を考えると SSG が総コスト最安。
- Eleventy は書いた HTML をそのまま出力し、クライアント JS を一切注入しない。
  「配信物は純静的・重いランタイム JS を持ち込まない」という guideline の精神は
  build 導入後も維持される(no-build は authoring ではなく配信の規律として再定義する)。
- Nunjucks の partial / macro / paired shortcode が theorem-card などの
  定理環境コンポーネントと相性がよい(`{% theorem %}...{% endtheorem %}` 形式)。
- collections から prev/next、sitemap.xml、llms.txt を自動生成でき、
  ルート増減時のドリフトが構造的に消える。

**制約: Node 依存は `website/` 配下に閉じ込める**(ユーザー要件)。
リポジトリルートに package.json を置かず、Lean / Rust のツールチェーンと混ぜない。

ディレクトリ構成(案):

```text
website/
  package.json / package-lock.json   Eleventy のみを依存に持つ
  eleventy.config.js
  .gitignore                          _site/ と node_modules/ を除外
  src/
    _layouts/     base.njk / article.njk / home.njk
    _includes/    header / footer / nav / OGP メタ / theorem 環境 macro 群
    _data/        site.json(ドメイン・著者)、nav.json(グローバルナビ)
    assets/       css/ js/ images(passthrough copy)
    index.njk、aat/**、sft/**、archsig/**、outreach/**(各ページ本文)
    sitemap.xml.njk / llms.txt.njk    collections から生成
    robots.txt / CNAME / _redirects   passthrough copy
  _site/          ビルド出力(コミットしない)
```

- ビルド出力 `_site/` はコミットしない。デプロイは Cloudflare Pages のビルドに任せる。
- ページ本文の authoring 形式は HTML(Nunjucks)を基本とする。定理環境が多い
  AAT / SFT ページは macro / shortcode で書き、markdown は使うとしても
  outreach 等の平文ページに限る(見た目の「markdown 生成感」回避とは独立の判断)。

### 4.2 デプロイ(確定: Cloudflare Pages git 連携ビルド)

2026-07-05 ユーザー決定(旧 2-a 案)。GitHub Actions は使わない。

- Pages プロジェクト設定: root directory = `website`、
  build command = `npx @11ty/eleventy`、output directory = `_site`。
- production branch = `main`。**ブランチごとに自動プレビュー URL が出る**ため、
  Wave 1 以降の各 PRD の受け入れテストはプレビュー URL 上の実ページ確認で行える。
- 移行手順: 現行の「`website/` を直接配信」から上記ビルド設定への切替は
  Pages ダッシュボード操作(ユーザー作業)。PRD-W0 の受け入れ手順に切替タイミングを
  明記する(ビルド設定切替前に main へ SSG 構成をマージすると配信が壊れるため、
  ブランチプレビューで検証 → 設定切替 → マージの順)。

### 4.3 CSS 分割

`assets/site.css` を役割別ファイルへ分割し、各ページから複数 `<link>` で読む
(HTTP/2 前提で実害なし。`@import` はウォーターフォールになるため使わない)。
分割ファイルは `website/src/assets/css/` に置き、Eleventy の passthrough copy で配信する。

```text
assets/css/
  tokens.css      デザイントークン(:root、dark/light の 4 系統上書きをここに集約)
  base.css        リセット、タイポグラフィ、リンク、skip-link
  layout.css      site-header / nav / footer / article-layout / sidebar / page-nav
  components.css  カード、テーブル、code-panel、パネル群(全セクション共通)
  theory.css      theorem-card / lean-status-card / status-badge / 定理環境の視覚言語
  home.css        トップページ専用(.home-page 上書きをすべてここへ隔離)
```

分割時の整理規律:

- 未使用カスタムプロパティ(191 定義中 実使用約 50)は、全 HTML の使用実態を機械的に
  棚卸ししてから削除する。トークンは「使われているものだけが定義される」状態にする。
- 同一セレクタの分散定義(`.status-list` ×3 など)を統合する。
- レスポンシブは各ファイル末尾に自ファイル分だけ置く(横断 responsive.css は作らない)。
- 各ファイル冒頭に目次コメントを置く。以後「1 ファイル 800 行超えたら分割を検討」を
  guideline に明文化する。

### 4.4 デザイン方針

目標: 「Markdown から生成した感」を消し、**数学モノグラフ / 研究出版物**として読める
佇まいにする。派手さは追加しない。

- **タイポグラフィ(serif / sans の役割再配分)**: 本文は現状すでに serif
  (Source Serif 4、18px / 1.68)だが、CSS 内で 54 箇所が sans 上書き・serif 指定は
  7 箇所しかなく、concept-grid やカード類など本文系コンポーネントの多くが sans に
  落ちている。これが「Markdown 生成感」の一因。Wave 0 の CSS 分割時に全上書きを
  棚卸しし、**sans は UI 要素(ナビ、バッジ、ボタン、表ヘッダ、キャプション)に
  限定**、本文系コンポーネントは serif 継承へ戻す。本文の行長を 65–75 字に制御し、
  行間・段落間隔をモノグラフ調に再調整する。
- **定理環境の視覚言語統一**: Definition / Proposition / Theorem / Proof idea /
  Example / Counterexample / Non-conclusion / Lean status を、色ではなく
  左罫線+ラベルの静かな環境スタイルで統一する(現行 theorem-card を核に再設計)。
  `proved` / `defined only` / `future obligation` / `empirical` のバッジ語彙は
  現行を継承する。
- **図式を一級市民にする**: AG 版の中心図式
  (Atom → site → ringed topos → law algebra → obstruction ideal → lawful locus →
  cohomology → derived → … → SAGA)を SVG で描き、AAT landing の主役に置く。
  各部ページ冒頭にも「全体図の中の現在地」ミニ図式を置く。数式画像化はしない
  (MathJax 継続)。
- **ArchView デモページ同梱(確定)**: `tools/archview/archview.html` は no-build
  単一 HTML(Three.js CDN + JSON 読み込み)なので、`/archsig/archview/` に
  サンプルデータ(`tools/archview/examples/seam-ignition/`)込みのデモページとして
  同梱する。H¹ obstruction の Gluing シーンは「理論が絵になる」最良の素材。
  v0.5.0 の ArchView 幾何再設計時にデモを差し替える前提とする。
- **抑制**: アニメーションは追加しない(reduced-motion 対応維持)。アクセント色は
  現行の系統を維持し、彩度を上げない。ヒーローの誇張・グラデーション大面積は避ける。

### 4.5 Wave 0 の受け入れ条件

- 既存 43 ページが Eleventy ビルド(テンプレート+分割 CSS)で見た目の劣化なく
  生成され、全ルートの URL が現状と一致する(directory route 維持)。
- Node 依存が `website/` 配下に閉じている(リポジトリルートに package.json /
  node_modules が現れない)。
- ナビ 1 項目の変更が単一ファイル(`_data/nav.json` またはテンプレート)修正で
  全ページへ波及する。
- sitemap.xml / llms.txt が collections からの生成物としてルート一覧と常に一致する。
- Cloudflare Pages のブランチプレビューでビルド・配信が確認でき、production 切替
  手順(ビルド設定変更 → マージ)が PRD に記録されている。
- Lighthouse(モバイル)で現状比劣化なし。ダークモード / reduced-motion 維持。
- `docs/website/guideline.md` に Eleventy 運用(preview コマンド、`_site/` 非コミット、
  passthrough 規約)と CSS 分割規律が追記されている。

## 5. Wave 1: AAT 全面リライト

### 5.1 ルート構成(確定: 正典 1:1 対応)

2026-07-05 ユーザー決定(B-1)。正典第I〜X部+付録に 1 ルートずつ対応させる。

```text
/aat/                                   Overview: 正典宣言、中心図式、claim taxonomy、読み順
/aat/atoms-objects-laws/                I.    Atom 公理系、configuration、molecule、architecture object
/aat/sites-and-sheaves/                 II.   architecture site、cover、restriction、descent の問い
/aat/law-algebra-lawful-locus/          III.  law algebra 層、obstruction ideal、Flat_U(X)=V(I_Ob^U)
/aat/obstruction-cohomology/            IV.   Čech H¹、local lawful と global lawful の差
/aat/derived-geometry-repair/           V.    law universe 交差、repair の derived 変形
/aat/singularity-monodromy-stack/       VI.   Tor による law conflict、monodromy、stack/gerbe
/aat/representations-periods/           VII.  graph/matrix/signature/period/distance の窓
/aat/measurement-theory/                VIII. 有限 measurement profile、unmeasured ≠ zero
/aat/evolution-geometry/                IX.   trace category、temporal coefficient、Lyapunov reading
/aat/semantic-repair-saga/              X.    SAGA: repair gluing = descent、SAGA 比較定理
/aat/appendix/                          付録: ambient convention、標準AGへの埋め込み、worked example
/aat/status/                            Lean status(AG 索引・proof obligations を典拠)
/aat/related-work/                      関連研究と novelty boundary(既存を AG 語彙で改訂)
```

- 採用理由: 正典との対応が自明で、source fidelity の点検・保守が最も安い。
  「docs の各部 ↔ website の各章」が 1:1 なので、正典改訂時の同期範囲が局所化する。
  DESIGN.md の「読者の現在地が見える粒度」にも合致する。
- 代償: 旧 15 ルートをほぼ全廃するため、リダイレクト整理が必要(後述 5.4)。
- 不採用案: 4 クラスタ再編(基礎 I–III / コホモロジーと修復 IV–VI /
  読みと計測 VII–IX / SAGA X)。正典との対応が崩れ同期コストが恒常化するため見送り。

### 5.2 各章ページの型

DESIGN.md の既存の型を継承する。

```text
章の位置づけ(全体図の中の現在地、1 段落)
→ Definition → Proposition / Theorem → Proof idea
→ Example → Counterexample / Non-conclusion
→ Lean status(theorem-card / lean-status-card で命題近接表示)

※ 正典への commit-pinned link は各章サイドバーに置かず、リファレンス面
(当面は /aat/ landing の About this edition)に集約する(2026-07-05 ユーザー決定)
```

規律(現行 DESIGN.md / guideline.md から継承、AG 版向けに再確認):

- website 独自の theorem claim を置かない。theorem ラベルの Lean proved 表示は
  `lean_theorem_index_ag_aat.md` に対応行がある場合のみ。それ以外は「本文内の数学命題」。
- claim taxonomy(Formal theorem / Certified bounded inference / Analytic reading)を
  landing で一度だけ説明し、各章はバッジで参照する。
- 防衛的な書き方をしない。non-conclusion は各命題の近くに最小限で置き、
  一覧を主役化しない(Tone Guide 継承)。
- 第X部 SAGA は理論のクライマックスとして landing / トップページから直接導線を張る。

### 5.3 ArchSig 概念章の先行増強(Wave 1 に同梱)

v0.4.0 → v0.5.0 で不変の内容だけを先に厚くする。

- `/archsig/`(landing): Skill-first の現行方針を維持しつつ、AG 計測 path を主役に書き直す。
- `/archsig/concepts/`(新設): 三層責務(ArchMap author / LawPolicy author / evaluator
  registry)、ArchMap / LawPolicy / MeasurementProfile の分離、5 値 verdict
  (measured_zero / measured_nonzero / unmeasured / unknown / not_computed)、
  「unmeasured is not zero」、ウィトゲンシュタイン的沈黙の規律。
- `/archsig/analyses/`(大幅増強): evaluator カタログを理論 anchor 付きで。
  ag.cech-obstruction ↔ 第IV部、ag.law-conflict-tor ↔ 第V/VI部、
  ag.period-stokes ↔ 第VII部、ag.sheaf-laplacian ↔ 第VIII部、という
  「何を測ると理論のどこを読んだことになるか」の対応表が中核。
- `/archsig/archview/`(新設): ArchView デモページ。`archview.html` を
  seam-ignition サンプルデータ込みで同梱し、Gluing & H¹ obstruction シーンを
  入口にする(§4.4 参照。v0.5.0 幾何再設計時に差し替え)。
- CLI 具体・schema 詳細・インストール手順は**この段階では増強しない**
  (v0.5.0 で全面変更されるため。現行記述の誤り修正のみ)。

注意: 動作例を載せる場合は `tools/archsig/tests/fixtures/ag_measurement/` または
`tools/archsig/examples/practical-rust-service/` を使う。`tests/fixtures/minimal/` は
v0 世代で現行 `analyze` に通らない(既知の破損。CLAUDE.md の例も同罪)。

### 5.4 旧ルートの処遇

旧 `aat/` 15 ルートのうち、B-1 でルート名が変わるものは Cloudflare Pages の
`_redirects` ファイルで 301 を張る(例: `/aat/atoms/ → /aat/atoms-objects-laws/`)。
`_redirects` は今回初導入になるため、Wave 0 で `website/src/` の passthrough copy
対象に含めておく。
sitemap / llms.txt は新ルートのみ列挙する。

### 5.5 Wave 1 の受け入れ条件

- `aat/` 全章が AG 正典第I〜X部+付録と 1:1 対応し、各章に Lean status 導線がある。
  正典への commit-pinned link はリファレンス面に集約されている。
- scheme / sheaf / cohomology / descent / SAGA が本文語彙として存在し、
  旧定式化(古典 AAT)の記述が「歴史的位置づけ」以外に残っていない。
- SAGA 章がトップ / AAT landing から 1 クリックで届く。
- ArchSig concepts / analyses が理論 anchor 対応表を持つ。
- 旧ルートからの 301 が機能し、リンク切れがない(Playwright で確認)。

## 6. Wave 2: SFT v2 リライト(発火条件付き・構成のみ固定)

発火条件: SFT P4(第V・VII・VIII部本文化)+ P5(README / aat_interface の v2 同期)完了。

- 現行 20 ページ(v1 三部構成: field-and-force / computation / software-evolution)は
  v2 の部構成(開発時空 / 力の幾何 / マージと降下 / 参加者と組織 / Conway 対応 /
  力学 / 変形と可能性 / 統計力学 / 観測と制御 / 寿命と長期挙動 + 付録)に合わせて
  再編する。ルート詳細は発火時の PRD で確定する(v2 本文がまだ動いているため、
  ここで固定すると website が正典に先行してしまう)。
- v1 語彙(ForecastCone / ConsequenceEnvelope)の扱いは `aat_interface.md` の
  v2 同期結果に従う。
- それまでの間、現行 SFT ページには手を入れない(Wave 0 の基盤移設のみ)。
  v1 のまま整合が取れており、中途半端な部分更新は語彙混在を生むだけ。

## 7. Wave 3: ArchSig 製品マニュアル完成(発火条件付き・構成のみ固定)

発火条件: ArchSig v0.5.0 出荷(compare / gate 一本化、単一契約版数 `<name>/v0.5.0`、
SAGA evaluator、`archsig-repair-plan/v1`)。

マニュアル構成(現行 6 ページ+concepts を発展させる):

```text
/archsig/                  landing: Skill-first、何が返ってくるか
/archsig/getting-started/  動く Quick Start(v0.5.0 fixture / example ベース)
/archsig/concepts/         Wave 1 で先行した責務境界・verdict 語彙(v0.5.0 語彙に更新)
/archsig/analyses/         evaluator カタログ+理論 anchor(SAGA evaluator 3 種を追加)
/archsig/manual/           artifact の読み方: measurement packet、summary、viewer、
                           repair-plan、gate 結果。「SAFE_WITHIN_POLICY を読む」を中心に
/archsig/reference/        CLI(archmap / law-policy / analyze / compare / gate /
                           schema-catalog)、schema、移行表(旧版との互換なしの明記)
/archsig/archview/         ArchView デモページ(Wave 1 で同梱済みのものを v0.5.0 幾何へ更新)
```

- 製品マニュアルの密度基準: 各章に「実行できるコマンド or 読める artifact 実例」が
  最低 1 つあること。H2 フラット構成を廃し、手順・例・境界を H3 で構造化する。
- SAGA の現場接続(第X部 ↔ repair-plan / SAGA evaluator)がマニュアルの目玉。
  Wave 1 の AAT SAGA 章と相互リンクする。
- FieldSig は製品マニュアル化しない。ArchSig / ArchView / FieldSig の三分業図を
  landing に置き、FieldSig は「進化計測レイヤー」として 1 節の予告に留める
  (SFT v2 と同期して育てる)。

## 8. docs/website/ 改訂プラン

website 本体と同時に、内部運用メモ `docs/website/` も本ノート基準へ改訂する。
改訂はコード変更と同じ PR に含め、website とメモが乖離した状態を main に残さない。

### 8.1 継続文書の改訂内容

**`guideline.md` — PR-W0 で改訂**

- 「stack / path」節を書き換える: 「no-build static stack」を**配信規律**として
  再定義(配信 artifact は純静的・クライアントに重いランタイム JS を持ち込まない)。
  authoring は Eleventy と明記する。
- Eleventy 運用の節を追加: preview は `npx @11ty/eleventy --serve`(旧
  `python3 -m http.server` 記述を置換)、`_site/` と `node_modules/` は非コミット、
  Node 依存は `website/` 配下限定、passthrough copy の対象
  (assets / robots.txt / CNAME / `_redirects`)。
- 検証節を更新: PR 前チェックに「Eleventy ビルドが警告なく通る」
  「生成ルート一覧が sitemap.xml / llms.txt と一致する(自動生成なので原則不一致は
  起きない。テンプレート変更時のみ確認)」を追加。
- CSS 分割規律を追加: ファイル構成(§4.3)、「1 ファイル 800 行超で分割検討」、
  トークンは使用実態のあるものだけ定義。

**`SITEMAP.md` — PR-W0 で縮退改訂、PR-W1a/b/c でルート表更新**

- sitemap.xml / llms.txt が collections からの自動生成になるため、本文書の役割を
  「canonical route と役割の一覧(人間向け)」に縮退させる。「sitemap.xml と
  一致させる」という手動同期規則は「生成元は Eleventy collections である」に置換。
- ルート表そのものは W1 の各 PR(AAT 14 ルート化、archsig 2 ルート追加、
  旧ルート廃止と `_redirects`)で更新する。

**`DESIGN.md` — PR-W1a で全面改訂(W0 では最小修正)**

- PR-W0 時点: stack 記述と preview 手順だけ Eleventy 基準に修正(ルート・成熟度表は
  旧内容のまま残す。W0 はコンテンツ不変のため)。
- PR-W1a で全面改訂:
  - トップレベル route 設計・ページネーション・読書導線を AG 版 14 ルート基準へ
    書き換え(§5.1 の構成を正とする)。
  - 「AAT publication edition の期待値」の型は継承しつつ、正典参照先を
    `docs/aat/algebraic_geometric_theory/` 第I〜X部+付録、Lean status 典拠を
    `lean_theorem_index_ag_aat.md` に更新。
  - 成熟度表・phase 管理(W2/W3/W4)を本ノートの Wave 0〜3 に置き換える。
    旧 W 番号と本ノートの Wave 番号の混同を避けるため、phase 名を
    `Wave 0(基盤)/ Wave 1(AAT+ArchSig 概念)/ Wave 2(SFT v2)/
    Wave 3(ArchSig マニュアル)` に統一する。
  - ArchSig page の参照元対応表を v0.4.0 実態(+ v0.5.0 予定の注記)に更新し、
    `/archsig/concepts/` と `/archsig/archview/` の行を追加。
- PR-W1b / W1c: 担当ルート分の成熟度表・参照元対応を追記。

**`README.md`(docs/website/)— PR-W0 で小改訂**

- 文書の分担一覧から退避済み計画書 3 本+方針メモを削除し、本ノート
  (`docs/note/website_renewal_design_note.md`)への参照を追加。
- stack 節(HTML / CSS / 小さな JavaScript / MathJax / Google Fonts)に
  Eleventy(authoring)を追記。

### 8.1.1 docs/website 外の同期対象

- `CLAUDE.md` / `AGENTS.md` の「検証コマンド」節にある website preview
  (`python3 -m http.server 0 --directory website`)を Eleventy 基準
  (`cd website && npx @11ty/eleventy --serve`)へ更新する(PR-W0)。

### 8.2 退避文書

`docs/archive/2026-07-website-renewal-superseded/` へ移動し、各ファイル冒頭に
退避理由と後継文書(本ノート)を 1 行で記す。

| 文書 | 退避時期 | 理由 |
| --- | --- | --- |
| `AAT_RENEWAL_PLAN.md` | PR-W1a | Atom refoundation 期の計画。AG 版 1:1 構成(§5)が後継 |
| `SFT_REWRITE_PLAN.md` | PR-W0 | v1 三部構成前提。Wave 2(§6)が後継 |
| `ARCHSIG_RENEWAL_PLAN.md` | PR-W1c | Skill-first 方針・Tone・分析カタログの素材を §5.3 / §7 と W1c 実装に吸収してから退避 |
| `archsig_website_improvement_policy.md` | PR-W1c | 同上 |

退避は「参照が残っていない」ことを確認してから行う(README / guideline /
DESIGN からのリンクを同 PR で除去)。

## 9. 実装体制と作業分割(確定: Claude 直接実装)

2026-07-05 ユーザー決定。web フロントは Codex の弱点のため、**今回のリニューアル
(Wave 0 / Wave 1)は通常の役割分担(Claude=PRD、Codex=実装)の例外として
Claude が直接実装する**。Codex 向け PRD は起こさず、本ノートを設計の正とし、
PR 単位で進める。受け入れテストはユーザーが Cloudflare Pages のブランチプレビューで行う。

```text
PR-W0    基盤刷新: Eleventy 化 + Pages ビルド切替 + CSS 分割 + デザインシステム
           + 既存 43 ページ移設
           (コンテンツ不変。見た目はタイポグラフィ・定理環境の刷新まで含む)
           docs 同期: guideline.md 改訂、SITEMAP.md 縮退、README.md 小改訂、
           DESIGN.md 最小修正、SFT_REWRITE_PLAN.md 退避(§8)
PR-W1a   AAT リライト前半: landing + 第I〜IV部(+ 中心図式 SVG、_redirects)
           docs 同期: DESIGN.md 全面改訂、AAT_RENEWAL_PLAN.md 退避(§8)
PR-W1b   AAT リライト後半: 第V〜X部 + 付録 + status + related-work
           docs 同期: DESIGN.md / SITEMAP.md のルート表更新
PR-W1c   ArchSig 先行増強: concepts / analyses / archview デモページ
           docs 同期: DESIGN.md 参照元対応表更新、ARCHSIG_RENEWAL_PLAN.md と
           archsig_website_improvement_policy.md を吸収後退避(§8)
Wave 2 / Wave 3   発火条件成立時に改めて計画(本ノート §6 §7 を骨格に、
           実装分担もその時点で判断)
```

- W0 を独立させる理由: 受け入れテストが「見た目の劣化なし」で完結し、
  コンテンツレビューと干渉しない。W1 は新基盤の上で書ける。
- W1 を分割する理由: 10 章+付録を 1 PR にするとレビューが重くなりすぎる。
  前半(I〜IV)で章の型が確定し、後半はその型の適用になる。ArchSig 増強は
  AAT 本文と独立にレビューできるため分離する。

## 10. 選択ポイントまとめ(2026-07-05 全件確定)

| # | 論点 | 決定 |
| --- | --- | --- |
| A | テンプレート機構・デプロイ | Eleventy SSG + Cloudflare Pages 連携ビルド(§4.1 / §4.2)。Node 依存は website/ 配下限定 |
| B | AAT ルート構成 | 正典 1:1 対応の 14 ルート(§5.1) |
| C | ArchView の website 掲載 | デモページとして Wave 1 で同梱(`/archsig/archview/`、seam-ignition サンプル込み)。v0.5.0 幾何再設計時に差し替え |
| D | 実装体制 | Claude 直接実装(役割分担の例外)。PRD なし、PR-W0 / W1a / W1b / W1c の 4 本(§9) |
| E | 本文書体 | 現状すでに本文 serif(Source Serif 4)であることを確認。serif 化ではなく sans 上書き 54 箇所の役割再配分を実施(§4.4) |

## 11. 本ノートが決めないこと

- SFT v2 / ArchSig v0.5.0 の完了時期(正典側・tooling 側の進行に従う)。
- website 上の新規 theorem claim・診断語彙(正典と tooling docs が先)。
- 日本語ミラー route(現行方針どおり作らない。outreach 導線のみ)。
