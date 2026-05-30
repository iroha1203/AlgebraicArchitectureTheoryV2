# Website 編集ガイドライン

この文書は `website` と `docs/website` を編集するときの作業方針をまとめる。

## 位置づけ

- `website/` は Cloudflare Pages 向けの public reading surface である。
- `docs/website/` は公開 artifact に含めない内部運用メモである。
- website は docs の複製ではない。AAT / SFT / ArchSig を公開向けに読むための web-native publication surface として扱う。
- AAT / SFT の公開ページは宣伝文ではなく、web-native preprint / monograph として、定義、前提、定理境界、例、反例、Lean status、non-conclusion を保つ。

## 編集方針

- website copy は `docs/website/README.md` の Tone Guide に従う。防衛的な書き方や否定から入る説明を避ける。
- 読者向け本文では「何を読めるか」「何を理解できるか」「どの概念へ進むか」を中心に書く。
- claim boundary、Lean status、Issue 管理、repository / docs の責務分離は編集時の制約として扱い、公開コピーにそのまま出さない。
- 理論上の新規 claim は先に `docs/aat/mathematical_theory/`、`docs/sft/software_field_theory.md`、`docs/sft/aat_interface.md`、または `docs/tool/` に反映する。
- ArchSig website では Core / Review の AAT structural surface と FieldSig 側の SFT / Operational / governance surface を分けて書く。
- 公開ページから `docs/website/` の内部設計メモへ誘導しない。

## stack / path

- 現在の website は no-build static stack として扱う。
- 重い frontend framework は、静的 HTML / CSS / 小さな JavaScript では足りない明確な理由がある場合だけ導入する。
- asset path は `assets/site.css` のような相対 path を使う。
- `/assets/site.css` のような root-absolute path は避ける。
- public page は directory route とし、各 route に `index.html` を置く。
- route を追加・削除・rename した場合は、`docs/website/SITEMAP.md`、`website/sitemap.xml`、`website/llms.txt` を合わせて確認する。
- production base URL は `https://iroha1203.dev/`、custom domain は `website/CNAME`、production sitemap は `website/sitemap.xml` で管理する。

## preview / 検証

directory route や `sitemap.xml` / `robots.txt` を確認する場合は、直接 HTML を開くより local server で確認する。

```bash
python3 -m http.server 0 --directory website
```

Codex から Playwright を実行する場合、macOS のブラウザ起動権限により通常の sandbox 内実行で Chromium が固まることがある。必要に応じて sandbox 外実行を使う。

PR 前には次を確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```

website 変更では、主要ページの title、link、asset path、layout、overflow を Playwright などで確認する。
