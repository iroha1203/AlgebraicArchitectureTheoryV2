# Website 運用メモ

このディレクトリは、公開 website のための非公開の運用メモを置く場所である。
公開される静的サイト本体は `../../website/` に置く。

`docs/website/` は GitHub Pages の artifact に含めない。公開ページ、asset、
`sitemap.xml`、`robots.txt`、`CNAME` は `website/` 側で管理する。

## 文書の分担

- [SITEMAP.md](SITEMAP.md): 公開 route、production `sitemap.xml`、`robots.txt` の対応を管理する。
- [DESIGN.md](DESIGN.md): website の設計方針、読者導線、ページネーション、本文成熟度、source mapping を管理する。

## 公開サイトの位置づけ

- `docs/` は研究本文、Lean status、proof obligation、tooling specification の source of truth として扱う。
- `website/` は GitHub Pages 向けの public reading surface として扱う。
- 公開サイトの canonical language は英語とする。
- 日本語の説明は Qiita、Zenn、Hashnode などの outreach article として扱い、必要に応じて canonical English pages へ戻す。
- AAT / SFT の公開ページは宣伝文ではなく、web-native preprint / monograph として、定義、前提、定理境界、例、反例、Lean status、non-conclusion を保つ。
- ArchSig ページでは Core、Review、SFT、Operational の product surface と、research gap / calibration gap / adapter boundary を分けて書く。

## 公開設定

- 公開ドメインは `iroha1203.dev`。
- custom domain は `website/CNAME` に記録する。
- production sitemap は `website/sitemap.xml` に置き、`https://iroha1203.dev/` を URL base とする。
- `website/robots.txt` は production sitemap を指す。
- GitHub Pages は `.github/workflows/pages.yml` で `website/` を artifact として deploy する。

## ローカル preview

repository root から次を実行する。

```bash
python3 -m http.server 8000 --directory website
```

その後、`http://localhost:8000/` を開く。

directory route や `sitemap.xml` / `robots.txt` を確認する場合は、直接 HTML を開くより
local server で確認する。

## path rules

- asset path は `assets/site.css` のような相対 path を使う。
- `/assets/site.css` のような root-absolute path は避ける。
- public page は directory route とし、各 route に `index.html` を置く。
- repository source document へリンクする場合は、公開 release では commit-pinned GitHub URL を使う。
- `docs/website/` の内部設計メモへ公開ページから誘導しない。

## stack

現在の website は no-build static stack として扱う。

- HTML
- CSS
- 小さな JavaScript
- MathJax CDN
- Google Fonts

重い frontend framework は、静的 HTML / CSS / 小さな JavaScript では足りない明確な理由がある場合だけ導入する。
