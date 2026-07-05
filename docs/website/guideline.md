# Website 編集ガイドライン

この文書は `website` と `docs/website` を編集するときの作業方針をまとめる。

## 位置づけ

- `website/` は Cloudflare Pages 向けの public reading surface である。
- `docs/website/` は公開 artifact に含めない内部運用メモである。
- website は docs の複製ではない。AAT / SFT / ArchSig を公開向けに読むための web-native publication surface として扱う。
- AAT / SFT の公開ページは宣伝文ではなく、web-native preprint / monograph として、定義、前提、定理境界、例、反例、Lean status、non-conclusion を保つ。
- 公開 surface では、AAT は Atom を公理とする純粋数学理論、ArchSig は Lean 証明器ではなく
  `ArchMap + LawPolicy + evidence contract` を読む Rust tool、として分けて説明する。

## 編集方針

- website copy は `docs/website/README.md` の Tone Guide に従う。防衛的な書き方や否定から入る説明を避ける。
- 読者向け本文では「何を読めるか」「何を理解できるか」「どの概念へ進むか」を中心に書く。
- claim boundary、Lean status、Issue 管理、repository / docs の責務分離は編集時の制約として扱い、公開コピーにそのまま出さない。
- ArchSig の説明では、`SAFE_WITHIN_POLICY` や `NO_SELECTED_OBSTRUCTION` のような選ばれた語彙内の
  肯定的診断を中心に置く。語れない外側は、長い non-conclusion ではなく必要最小限の boundary として扱う。
- 公開ページや renewal plan では、読者が検討できる具体的な artifact / theorem / example / command を中心にする。
  一般的に証明できない巨大 claim の否定を、見出しや残タスクの中心にしない。
- 理論上の新規 claim は先に `docs/aat/algebraic_geometric_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、または `docs/tool/` に反映する。
- ArchSig website では Core / Review の AAT structural surface と FieldSig 側の SFT / Operational / governance surface を分けて書く。
- 公開ページから `docs/website/` の内部設計メモへ誘導しない。

## stack / path

- 配信 artifact は純静的とする(no-build は**配信の規律**)。クライアントに重い
  ランタイム JS / frontend framework を持ち込まない。
- authoring は Eleventy(SSG)で行う。`website/src/` が入力、`website/_site/` が
  ビルド出力であり、`_site/` と `node_modules/` はコミットしない。
- Node 依存(package.json / package-lock.json)は `website/` 配下に限定し、
  リポジトリルートへ持ち出さない。
- 共通レイアウトは `src/_layouts/base.njk`、ヘッダ / フッターは `src/_includes/`、
  グローバルナビは `src/_data/nav.json` で管理する。ページ本文は front matter 付き
  `src/**/index.html` に置く。
- `sitemap.xml` / `llms.txt` は collections からの自動生成(`src/sitemap.njk` /
  `src/llms.njk`)。手動同期しない。ページの表示順・llms ラベルは各ページの
  front matter(`order` / `llmsLabel`)で管理する。
- 静的ファイル(`assets/`、`robots.txt`、`CNAME`、`_redirects`)は passthrough copy。
  対象は `eleventy.config.js` に登録する。
- asset path は `assets/css/base.css` のような相対 path を使う
  (layout 側は `relprefix` filter が付与する)。root-absolute path は避ける。
- public page は directory route とし、各 route に `index.html` を置く。
- production base URL は `https://iroha1203.dev/`、custom domain は `website/CNAME`。
  Cloudflare Pages は root directory `website`、build command `npx @11ty/eleventy`、
  output directory `_site` でビルド配信する。

## CSS 分割規律

- CSS は `src/assets/css/` の役割別ファイルで管理する:
  `tokens`(デザイントークン、テーマ4系統)/ `base`(要素既定)/
  `layout`(ページ骨格)/ `components`(共有コンポーネント)/
  `theory`(定理環境)/ `home`(トップ専用。トップページだけが読み込む)。
- 1 ファイルが 800 行を超えたら分割を検討する。
- トークンは使用実態のあるものだけ定義する。どのページからも使われない
  コンポーネント規則を残さない。
- 書体の役割: 本文系は serif(Source Serif 4、読み込みレンジ wght 400–700)、
  sans は UI 要素(ナビ、バッジ、ラベル、表ヘッダ、キャプション、サイドパネル)に
  限定する。

## preview / 検証

```bash
cd website && npm install        # 初回のみ
npx @11ty/eleventy --serve       # local preview(ビルド+watch)
```

directory route や `sitemap.xml` / `robots.txt` を確認する場合は、直接 HTML を開くより
上記の dev server(または `python3 -m http.server 0 --directory website/_site`)で
確認する。PR 前には `npx @11ty/eleventy` が警告なく通ることを確認する。

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがある。必要に応じて sandbox 外実行を使う。

PR 前には次を確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```

website 変更では、主要ページの title、link、asset path、layout、overflow を Playwright などで確認する。
