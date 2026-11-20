# Website 編集ガイドライン

この文書は、`website` と `docs/website` を編集するときの作業方針を定める。

## 位置づけ

- `website/` は Cloudflare Pages 向けの公開サイトである。
- `docs/website/` は公開物に含めない内部の運用メモである。
- website は研究 docs の単なる複製ではなく、AAT・SFT・ArchSig を公開向けに読みやすく構成する場として扱う。
- AAT / SFT の公開ページは宣伝文ではなく、ウェブ向けのプレプリントやモノグラフとして、
  定義、前提、定理の適用範囲、例、反例、Lean の証明状態、非結論を正確に保つ。
- 公開説明に用いる AAT の理論本体の所在は
  [AGENTS.md「理論本文の参照先」](../../AGENTS.md#理論本文の参照先)に、
  ArchSig の入力と計算の責務は [Tool guideline](../tool/guideline.md#責務範囲入力トライアドの正本)にある。

## 編集方針

- 公開ページの文面は `docs/website/README.md` の Tone Guide に従う。防衛的な書き方や否定から入る説明を避ける。
- 読者向けの本文では「何を読めるか」「何を理解できるか」「どの概念へ進むか」を中心に書く。
- 主張範囲の規律、Lean の状態管理、Issue 管理、リポジトリ内の文書責務の分担は編集時の制約として扱い、
  公開ページの文面にそのまま持ち込まない。
- ArchSig の説明では、`SAFE_WITHIN_POLICY` や `NO_SELECTED_OBSTRUCTION` のように選んだ語彙の中で
  言える肯定的な診断を中心に置く。語れない外側は、長大な非結論一覧にせず必要最小限の限定として扱う。
- 公開ページや刷新計画では、読者が検討できる具体的な成果物・定理・例・コマンドを中心に据える。
  一般的に証明できない巨大な主張の否定を、見出しや残タスクの中心にしない。
- 理論上の新しい主張は、先に `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、
  `docs/sft/aat_interface.md`、または `docs/tool/` へ反映する。
- ArchSig の公開ページでは、Core / Review に対応する AAT の構造解析と、FieldSig 側の
  SFT・運用・ガバナンスの解析を分けて書く。
- 公開ページから `docs/website/` にある内部設計メモへ誘導しない。
- Website の恒久情報は、このガイドライン、`DESIGN.md`、`SITEMAP.md`、および現行の website ソースに置く。

## stack / path

- 配信物は純粋な静的ファイルとする（クライアント側で重い実行時 JS やフロントエンドフレームワークを持ち込まない）。
- 執筆とビルドは Eleventy（SSG）で行う。`website/src/` が入力、`website/_site/` がビルド出力であり、
  `_site/` と `node_modules/` はコミットしない。
- Node 依存（`package.json` / `package-lock.json`）は `website/` 配下に限定し、
  リポジトリルートへ置かない。
- 共通レイアウトは `src/_layouts/base.njk`、ヘッダー・フッターは `src/_includes/`、
  グローバルナビは `src/_data/nav.json` で管理する。ページ本文は front matter 付きの
  `src/**/index.html` に置く。
- `sitemap.xml` と `llms.txt` は collections から自動生成する（`src/sitemap.njk` /
  `src/llms.njk`）。手動で同期しない。ページの表示順と llms ラベルは各ページの
  front matter（`order` / `llmsLabel`）で管理する。
- 静的ファイル（`assets/`、`robots.txt`、`CNAME`、`_redirects`）はそのままコピー（passthrough copy）する。
  対象は `eleventy.config.js` に登録する。
- アセットパスは `assets/css/base.css` のような相対パスを使う
  （レイアウト側で `relprefix` フィルタが付与する）。ルート絶対パスは避ける。
- 公開ページはディレクトリ単位のルート構成とし、各ルートに `index.html` を置く。
- 本番のベース URL は `https://iroha1203.dev/`、カスタムドメインは `website/CNAME` にある。
  Cloudflare Pages はルートディレクトリ `website`、ビルドコマンド `npx @11ty/eleventy`、
  出力ディレクトリ `_site` でビルド・配信する。

## CSS 分割規律

- CSS は `src/assets/css/` に役割別ファイルで管理する:
  `tokens`（デザイントークン、テーマ4系統）、`base`（要素の既定スタイル）、
  `layout`（ページ骨格）、`components`（共有コンポーネント）、
  `theory`（定理環境）、`home`（トップページ専用。トップページだけが読み込む）。
- 1 ファイルが 800 行を超えたら分割を検討する。
- トークンは実際に使われているものだけ定義し、どのページからも使われないコンポーネント規則を残さない。
- 書体の役割分担: 本文系は serif（Source Serif 4、読み込みウェイト 400–700）、
  sans は UI 要素（ナビ、バッジ、ラベル、表ヘッダー、キャプション、サイドパネル）に限定する。

## preview / 検証

```bash
cd website && npm install        # 初回のみ
npx @11ty/eleventy --serve       # ローカルプレビュー（ビルド＋監視）
```

ディレクトリ単位のルートや `sitemap.xml` / `robots.txt` を確認する場合は、HTML を直接開くのではなく、
上記の開発サーバ（または `python3 -m http.server 0 --directory website/_site`）で確認する。
PR 前には `npx @11ty/eleventy` が警告なく完了することを確認する。

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常のサンドボックス内実行で
Chromium が固まることがある。必要に応じてサンドボックス外実行を使う。

PR 前の共通チェックは [Workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。

website の変更では、主要ページの title、リンク、アセットパス、レイアウト、はみ出し（overflow）を
Playwright などで確認する。
