# Website 運用メモ

このディレクトリは、公開 website のための非公開の運用メモを置く場所である。
公開される静的サイト本体は `../../website/` に置く。

`docs/website/` は Cloudflare Pages の公開 artifact に含めない。公開ページ、asset、
`sitemap.xml`、`robots.txt`、`CNAME` は `website/` 側で管理する。

## 文書の分担

- [guideline.md](guideline.md): website 編集方針、claim boundary、path rule、preview / 検証を管理する。
- [SITEMAP.md](SITEMAP.md): 公開 route、production `sitemap.xml`、`robots.txt` の対応を管理する。
- [DESIGN.md](DESIGN.md): website の設計方針、読者導線、ページネーション、本文成熟度、source mapping を管理する。
- [AAT_RENEWAL_PLAN.md](AAT_RENEWAL_PLAN.md): Atom refoundation 後の AAT website を web-native monograph として再構成するための計画書。
- [SFT_REWRITE_PLAN.md](SFT_REWRITE_PLAN.md): SFT website を既存 Part 構成から削除して三部構成で書き直すための複数セッション向け計画書。
- [ARCHSIG_RENEWAL_PLAN.md](ARCHSIG_RENEWAL_PLAN.md): ArchSig website を LLM Skill-first の Web PR 面 & マニュアルとして章立てから書き直すための計画書。
- [archsig_website_improvement_policy.md](archsig_website_improvement_policy.md): ArchSig website を公開製品マニュアルとして改善するための方針メモ。

## 公開サイトの位置づけ

- `docs/` は研究本文、Lean status、proof obligation、tooling specification の source of truth として扱う。
- `website/` は Cloudflare Pages 向けの public reading surface として扱う。
- AAT の数学的正典は `docs/aat/algebraic_geometric_theory/` であり続ける。
  `website/aat/**` はそれを置き換えず、出版物として肉付けした web-native
  monograph / publication edition として扱う。
- AAT website では、定義、命題、証明アイデア、例、反例、Lean status を章本文の中で
  追跡できるようにする。website 独自の theorem claim は置かず、理論上の新規 claim は
  先に `docs/aat/algebraic_geometric_theory/` に反映する。
- 公開サイトの canonical language は英語とする。
- 日本語の説明は Qiita、Zenn、Hashnode などの outreach article として扱い、必要に応じて canonical English pages へ戻す。
- AAT / SFT の公開ページは宣伝文ではなく、web-native preprint / monograph として、定義、前提、定理境界、例、反例、Lean status、non-conclusion を保つ。
- ArchSig ページでは Core、Review、SFT、Operational の product surface と、research gap / calibration gap / adapter boundary を分けて書く。
- repository、docs、Lean status、Issue、claim boundary への言及は、公開コピーへそのまま出すための素材ではない。これらは編集時の制約として扱い、本文では読者にとって自然な研究内容、読書導線、概念説明へ翻訳する。
- landing page や section copy では、内部の根拠管理、進捗管理、運用方針を説明しない。公開本文は「何を読めるか」「何を理解できるか」「どの概念へ進むか」を中心に書く。

## Tone Guide

* 防衛的な書き方を避ける。
* 否定から入らない。
* 以下のような表現を好む。

```text
SFT studies ...
SFT defines ...
SFT computes ...
SFT systematizes ...
SFT makes ... computable.
SFT treats ... as ...
```

* 研究対象を堂々と宣言する。
* 境界や注意書きは必要なら Reference / Formal Core 側に置く。

## 公開設定

- 公開ドメインは `iroha1203.dev`。
- custom domain は `website/CNAME` に記録する。
- production sitemap は `website/sitemap.xml` に置き、`https://iroha1203.dev/` を URL base とする。
- `website/robots.txt` は production sitemap を指す。
- Cloudflare Pages は `website/` を公開ディレクトリとして deploy する。

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
