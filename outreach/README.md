# Outreach

このディレクトリは、AAT / SFT / ArchSig の研究成果を外部へ展開するための出版素材を管理する。
記事本文、翻訳、公開前の下書き、記事用画像を置き、数学本文・Lean status・tooling仕様の source of truth にはしない。

## 構成

- `blog/hashnode/`: 英語記事(Hashnode ほか英語媒体向け)
- `blog/zenn/`: 日本語記事・下書き(Zenn ほか日本語媒体向け)
- `blog/assets/`: 記事用画像
- `paper/saga/`: SAGA 論文(Zenodo 出版素材・LaTeX 原稿・bundle スクリプト)

公開 website の `/outreach/` は `website/src/outreach/` で管理する。ここにある記事本文は公開サイトの実装そのものではなく、外部媒体向けの原稿・素材である。

研究上の canonical source は、記事からリンクしている AAT / SFT / tooling の各 source of truth とする。記事の記述がそれらを置き換えることはない。
